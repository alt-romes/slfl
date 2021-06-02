{-# LANGUAGE LambdaCase #-}
module Evaluate where

import Data.List
import Data.Maybe

import CoreSyntax
import Util

import Debug.Trace

-- TODO: https://hackage.haskell.org/package/containers-0.4.0.0/docs/Data-Map.html

type BoundCtxt = [CoreExpr]
type FreeCtxt = [(String, CoreExpr)]
type Ctxt = (BoundCtxt, FreeCtxt)

-- Note: the typechecker should make sure the expression is valid 

substitute :: CoreExpr -> CoreExpr -> CoreExpr
substitute = substitute' 0
    where
        substitute' :: Int -> CoreExpr -> CoreExpr -> CoreExpr
        substitute' d bl@(BLVar x) v = if x == d then v else bl
        substitute' d bu@(BUVar x) v = if x == d then v else bu
        substitute' d (Abs t e) v = Abs t $ substitute' (d+1) e v
        substitute' d (App e1 e2) v = App (substitute' d e1 v) (substitute' d e2 v)
        substitute' d (TensorValue e1 e2) v = TensorValue (substitute' d e1 v) (substitute' d e2 v)
        substitute' d (LetTensor e1 e2) v = LetTensor (substitute' d e1 v) (substitute' d e2 v)
        substitute' d (LetUnit e1 e2) v = LetUnit (substitute' d e1 v) (substitute' d e2 v)
        substitute' d (WithValue e1 e2) v = WithValue (substitute' d e1 v) (substitute' d e2 v)
        substitute' d (Fst e) v = Fst $ substitute' d e v
        substitute' d (Snd e) v = Snd $ substitute' d e v
        substitute' d (InjL t e) v = InjL t $ substitute' d e v
        substitute' d (InjR t e) v = InjR t $ substitute' d e v
        substitute' d (CaseOfPlus e1 e2 e3) v = CaseOfPlus (substitute' d e1 v) (substitute' d e2 v) (substitute' d e3 v)
        substitute' d (BangValue e) v = BangValue (substitute' d e v)
        substitute' d (LetBang e1 e2) v = LetBang (substitute' d e1 v) (substitute' d e2 v)
        substitute' d (IfThenElse e1 e2 e3) v = IfThenElse (substitute' d e1 v) (substitute' d e2 v) (substitute' d e3 v)
        substitute' d (LetIn e1 e2) v = LetIn (substitute' d e1 v) (substitute' d e2 v)
        substitute' d e v = e      -- atomic expressions

-- eval --- Ctxt, CoreExpr -> CoreExpr 
eval :: Ctxt -> CoreExpr -> CoreExpr

--- hyp --------------------

eval c@(bctxt, _) (BLVar x) = eval c $ bctxt !! x

eval c@(_, fctxt) (FLVar x) = eval c $ fromJust $ lookup x fctxt

eval c@(bctxt, _) (BUVar x) = eval c $ bctxt !! x

eval c@(_, fctxt) (FUVar x) = eval c $ fromJust $ lookup x fctxt

--- -o ---------------------

--  -oI
eval _ (Abs t e) = Abs t e

--  -oE
eval ctxt@(bctxt, fctxt) (App e1 e2) =
    let (Abs _ e1') = eval ctxt e1 in
    let v = eval ctxt e2 in
        let e1'' = substitute e1' v in
            eval (v:bctxt, fctxt) e1''

--- * ----------------------

--  *I
--
eval c (TensorValue e1 e2) =
    let e1' = eval c e1 in
    let e2' = eval c e2 in
    TensorValue e1' e2'

--  *E
eval ctxt@(bctxt, fctxt) (LetTensor e1 e2) =
    let TensorValue e3 e4 = eval ctxt e1 in
    eval (e4:e3:bctxt, fctxt) e2

--- 1 ----------------------

--  1I
eval _ UnitValue = UnitValue

--  1E
eval ctxt (LetUnit e1 e2) =
    let UnitValue = eval ctxt e1 in
    eval ctxt e2

--- & ----------------------

--  &I
eval ctxt (WithValue e1 e2) =
    let e1' = eval ctxt e1 in
    let e2' = eval ctxt e2 in
    WithValue e1' e2'

--  &E
eval ctxt (Fst e) =
    let WithValue e1 e2 = eval ctxt e in
    eval ctxt e1

--  &E
eval ctxt (Snd e) =
    let WithValue e1 e2 = eval ctxt e in
    eval ctxt e2

--- + ----------------------

--  +I
eval ctxt (InjL t e) =
    let e' = eval ctxt e in
    InjL t e'

--  +I
eval ctxt (InjR t e) =
    let e' = eval ctxt e in
    InjR t e'

--  +E
eval ctxt (CaseOfPlus e1 e2 e3) =
    let e1' = eval ctxt e1 in
    let (bctxt, fctxt) = ctxt in
    case e1' of
        (InjL t e) -> eval (e1':bctxt, fctxt) e2
        (InjR t e) -> eval (e1':bctxt, fctxt) e3

--- ! ----------------------

--  !I
eval ctxt (BangValue e) =
    let e' = eval ctxt e in
    BangValue e'

--  !E
eval ctxt@(bctxt, fctxt) (LetBang e1 e2) =
    let BangValue e1' = eval ctxt e1 in
    eval (e1':bctxt, fctxt) e2

--- LetIn -----------------

eval ctxt@(bctxt, fctxt) (LetIn e1 e2) =
    let e1v = eval ctxt e1 in
    eval (e1v:bctxt, fctxt) e2

--- Mark for synthesis ---

eval _ (Mark _ _ t) = errorWithoutStackTrace $ "[Eval] Can't eval synthesis marker:\n    " ++ show t

--- Bool -------------------

eval ctxt Tru = Tru
eval ctxt Fls = Fls

eval ctxt (IfThenElse e1 e2 e3) =
    let cond = eval ctxt e1 in
    case cond of
        Tru -> eval ctxt e2
        Fls -> eval ctxt e3

--- Sum Type ---------------

eval ctxt (SumValue mts (tag, e)) =
    let e' = eval ctxt e in
    SumValue mts (tag, e')

eval ctxt@(bctxt, fctxt) (CaseOfSum e1 exps) =
    let SumValue mts (tag, e) = eval ctxt e1 in
        let expbranch = fromJust $ lookup tag exps in -- If it's well typed we can assume the lookup to work
            eval (e:bctxt, fctxt) expbranch

-- end eval ------------



---- TOP LEVEL ------------

evalExpr :: CoreExpr -> CoreExpr
evalExpr = eval ([], [])

evalModule :: [CoreBinding] -> CoreExpr
evalModule cbs =
    case find (\(CoreBinding n _) -> n == "main") cbs of
      Nothing -> errorWithoutStackTrace "[Eval] No main function defined."
      Just (CoreBinding _ exp) -> eval ([], map (\(CoreBinding n e) -> (n, e)) cbs) exp


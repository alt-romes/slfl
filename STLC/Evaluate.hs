module Evaluate where

import Data.Maybe

import CoreSyntax
import LinearCheck hiding (BoundCtxt, FreeCtxt, Ctxt, equalCtxts)

type BoundCtxt = [CoreExpr]
type FreeCtxt = [(Name, CoreExpr)]
type Ctxt = (BoundCtxt, FreeCtxt)

-- eval --- Ctxt, CoreExpr -> CoreExpr 
-- typechecker should make sure the expression is valid
eval :: Ctxt -> CoreExpr -> CoreExpr

--- hyp --------------------

eval (bctxt, _) (BLVar x) = bctxt !! x

eval (_, fctxt) (FLVar x) = fromJust $ lookup x fctxt

eval (bctxt, _) (BUVar x) = bctxt !! x

eval (_, fctxt) (FUVar x) = fromJust $ lookup x fctxt

--- -o ---------------------

--  -oI
eval _ (Abs t e) = Abs t e

--  -oE
eval ctxt (App e1 e2) =
    let Abs _ e1' = eval ctxt e1 in
    let v = eval ctxt e2 in
    let (bctxt, fctxt) = ctxt in
    eval (v:bctxt, fctxt) e1'

--- * ----------------------

--  *I
eval ctxt (TensorValue e1 e2) =
    let e1' = eval ctxt e1 in
    let e2' = eval ctxt e2 in
    TensorValue e1' e2'

--  *E
eval ctxt (LetTensor e1 e2) =
    let TensorValue e3 e4 = eval ctxt e1 in
    let (bctxt, fctxt) = ctxt in
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
eval ctxt (LetBang e1 e2) =
    let BangValue e1' = eval ctxt e1 in
    let (bctxt, fctxt) = ctxt in
    eval (e1':bctxt, fctxt) e2


--- Bool -------------------

eval ctxt Tru = Tru
eval ctxt Fls = Fls

eval ctxt (IfThenElse e1 e2 e3) =
    let cond = eval ctxt e1 in
    case cond of
        Tru -> eval ctxt e2
        Fls -> eval ctxt e3

-- end eval ------------



-- top level ---------------


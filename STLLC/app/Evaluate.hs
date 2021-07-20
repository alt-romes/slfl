{-# LANGUAGE LambdaCase #-}
module Evaluate (evalExpr, evalModule) where

import Data.List
import Data.Maybe
import Debug.Trace
import Control.Monad.State
import Control.Monad.Reader


import CoreSyntax
import Program
import Util



type BoundCtxt = [CoreExpr]
type FreeCtxt = [(String, CoreExpr)]
type Ctxt = (BoundCtxt, FreeCtxt)

-------------------------------------------------------------------------------
-- Functions
-------------------------------------------------------------------------------

substitute :: CoreExpr -> CoreExpr -> CoreExpr
substitute e v = evalState (transformM (substitute' v) e) 0
    where
        substitute' :: CoreExpr -> CoreExpr -> State Int CoreExpr
        substitute' v bl@(BLVar x) = do
            d <- get
            if x == d
               then return v
               else return bl
        substitute' v bu@(BUVar x) = do
            d <- get
            if x == d
               then return v
               else return bu
        substitute' v e = return e





-- Note: the typechecker should have already made sure the expression is valid 
-------------------------------------------------------------------------------
-- Main Logic
-------------------------------------------------------------------------------

eval :: Ctxt -> CoreExpr -> ReaderT [ADTD] Maybe CoreExpr

--- hyp --------------------

eval c@(bctxt, _) (BLVar x) = eval c $ bctxt !! x

eval c@(_, fctxt) (FLVar x) = eval c $ fromJust $ lookup x fctxt

eval c@(bctxt, _) (BUVar x) = eval c $ bctxt !! x

eval c@(_, fctxt) (FUVar x) = case lookup x fctxt of
                                     Just f -> eval c f
                                     Nothing -> do -- Couldn't find free variable in unrestricted context, so it's an ADT constructor (function that returns adt value)
                                         adts <- ask
                                         let argument = case lookup x $ concatMap (\(ADTD _ _ ns) -> ns) adts of 
                                                          Just t ->
                                                              case t of
                                                                Unit -> Nothing
                                                                _ -> Just $ BLVar 0 in
                                             return (Abs Nothing (ADTVal x argument))

--- -o ---------------------

--  -oI
eval _ (Abs t e) = return $ Abs t e

--  -oE
eval ctxt@(bctxt, fctxt) (App e1 e2) = do
    Abs _ e1' <- eval ctxt e1
    v <- eval ctxt e2
    let e1'' = substitute e1' v in
        eval (v:bctxt, fctxt) e1''

--- * ----------------------

--  *I
eval c (TensorValue e1 e2) = do
    e1' <- eval c e1
    e2' <- eval c e2
    return $ TensorValue e1' e2'

--  *E
eval ctxt@(bctxt, fctxt) (LetTensor e1 e2) = do
    TensorValue e3 e4 <- eval ctxt e1
    eval (e4:e3:bctxt, fctxt) e2

--- 1 ----------------------

--  1I
eval _ UnitValue = return UnitValue

--  1E
eval ctxt (LetUnit e1 e2) = do
    UnitValue <- eval ctxt e1
    eval ctxt e2

--- & ----------------------

--  &I
eval ctxt (WithValue e1 e2) = do
    e1' <- eval ctxt e1
    e2' <- eval ctxt e2
    return $ WithValue e1' e2'

--  &E
eval ctxt (Fst e) = do
    WithValue e1 e2 <- eval ctxt e
    eval ctxt e1

--  &E
eval ctxt (Snd e) = do
    WithValue e1 e2 <- eval ctxt e
    eval ctxt e2

--- + ----------------------

--  +I
eval ctxt (InjL t e) = do
    e' <- eval ctxt e
    return $ InjL t e'

--  +I
eval ctxt (InjR t e) = do
    e' <- eval ctxt e
    return $ InjR t e'

--  +E
eval c@(bctxt, fctxt) (CaseOfPlus e1 e2 e3) = do
    e1' <- eval c e1
    case e1' of
        (InjL t e) -> eval (e1':bctxt, fctxt) e2
        (InjR t e) -> eval (e1':bctxt, fctxt) e3

--- ! ----------------------

--  !I
eval ctxt (BangValue e) = do
    e' <- eval ctxt e
    return $ BangValue e'

--  !E
eval ctxt@(bctxt, fctxt) (LetBang e1 e2) = do
    BangValue e1' <- eval ctxt e1
    eval (e1':bctxt, fctxt) e2

--- LetIn -----------------

eval ctxt@(bctxt, fctxt) (LetIn e1 e2) = do
    e1v <- eval ctxt e1
    eval (e1v:bctxt, fctxt) e2

--- Mark for synthesis ---

eval _ (Mark _ _ _ t _) = errorWithoutStackTrace $ "[Eval] Can't eval synthesis marker:\n    " ++ show t

--- Sum Type ---------------

eval ctxt (SumValue mts (tag, e)) = do
    e' <- eval ctxt e
    return $ SumValue mts (tag, e')

eval ctxt@(bctxt, fctxt) (CaseOfSum e1 exps) = do
    SumValue mts (tag, e) <- eval ctxt e1
    let expbranch = fromJust $ lookup tag exps -- If it's well typed we can assume the lookup to work
    eval (e:bctxt, fctxt) expbranch

eval c (ADTVal x y) = return (ADTVal x y)

eval c (CaseOf _ _) = error "Case Of"

eval c (Lit x) = return (Lit x)



-------------------------------------------------------------------------------
-- Exported Functions
-------------------------------------------------------------------------------

evalExpr :: CoreExpr -> CoreExpr
evalExpr e = fromJust $ runReaderT (eval ([], []) e) []

evalModule :: Program -> CoreExpr
evalModule (Program adts _ _ cbs) =
    case find (\(CoreBinding n _) -> n == "main") cbs of
      Nothing -> errorWithoutStackTrace "[Eval] No main function defined."
      Just (CoreBinding _ exp) -> fromJust $ runReaderT (eval ([], map (\(CoreBinding n e) -> (n, e)) cbs) exp) adts


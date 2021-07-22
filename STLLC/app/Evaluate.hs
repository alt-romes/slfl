{-# LANGUAGE LambdaCase #-}
module Evaluate (evalExpr, evalModule) where

import Data.List
import Data.Bifunctor
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
substitute = substitute' 0
    where
        substitute' :: Int -> CoreExpr -> CoreExpr -> CoreExpr
        substitute' d (CExpBop n e1 e2) v = CExpBop n (substitute' d e1 v) (substitute' d e2 v)
        substitute' d bl@(BLVar x) v = if x == d then v else bl
        substitute' d bu@(BUVar x) v = if x == d then v else bu
        substitute' d (Abs t e) v = Abs t $ substitute' (d+1) e v
        substitute' d (App e1 e2) v = App (substitute' d e1 v) (substitute' d e2 v)
        substitute' d (TensorValue e1 e2) v = TensorValue (substitute' d e1 v) (substitute' d e2 v)
        substitute' d (LetTensor e1 e2) v = LetTensor (substitute' d e1 v) (substitute' (d+2) e2 v)
        substitute' d (LetUnit e1 e2) v = LetUnit (substitute' d e1 v) (substitute' d e2 v)
        substitute' d (WithValue e1 e2) v = WithValue (substitute' d e1 v) (substitute' d e2 v)
        substitute' d (Fst e) v = Fst $ substitute' d e v
        substitute' d (Snd e) v = Snd $ substitute' d e v
        substitute' d (InjL t e) v = InjL t $ substitute' d e v
        substitute' d (InjR t e) v = InjR t $ substitute' d e v
        substitute' d (CaseOfPlus e1 e2 e3) v = CaseOfPlus (substitute' d e1 v) (substitute' (d+1) e2 v) (substitute' (d+1) e3 v)
        substitute' d (BangValue e) v = BangValue (substitute' d e v)
        substitute' d (LetBang e1 e2) v = LetBang (substitute' d e1 v) (substitute' (d+1) e2 v)
        substitute' d (LetIn e1 e2) v = LetIn (substitute' d e1 v) (substitute' (d+1) e2 v)
        substitute' d (SumValue _ _) v = undefined
        substitute' d (CaseOfSum _ _) v = undefined
        substitute' d (CaseOf e ls) v = CaseOf (substitute' d e v) (map (second $ \e' -> substitute' (d+1) e' v) ls)
        substitute' d (ADTVal e (Just ls)) v = ADTVal e (Just $ substitute' d ls v)

        substitute' d e v = e      -- atomic expressions

        -- substitute' v adtv@(ADTVal _ (Just x)) = return x
        -- substitute' v adtv@(ADTVal _ Nothing) = error "[Eval] This shouldn't happen right? :)"





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
                                         case lookup x $ concatMap (\(ADTD _ _ ns) -> ns) adts of 
                                            Just t ->
                                              case t of
                                                Unit -> return $ ADTVal x Nothing
                                                _ -> return (Abs Nothing (ADTVal x (Just $ BLVar 0)))

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

eval c@(bctxt, fctxt) (CaseOf e ls) = do
    ADTVal nam arg <- eval c e
    let bctxt' = case arg of Just arge -> arge:bctxt; Nothing -> UnitValue:bctxt
    case lookup nam ls of
      Nothing -> error "[Eval] Couldn't find constructor..."
      Just e' -> eval (bctxt', fctxt) e'

eval c (Lit x) = return (Lit x)

eval c (CExpBop n x y) =
    case n of
      "+" -> evalInts >>= \(x',y') -> return $ Lit $ LitInt (x' + y')
      "*" -> evalInts >>= \(x',y') -> return $ Lit $ LitInt (x' * y')
      "-" -> evalInts >>= \(x',y') -> return $ Lit $ LitInt (x' - y')
      "==" -> do
        x' <- eval c x
        y' <- eval c y
        return $ ADTVal (show $ x' == y') Nothing
      "!=" -> do
        x' <- eval c x
        y' <- eval c y
        return $ ADTVal (show $ x' /= y') Nothing
      ">=" -> evalInts >>= \(x', y') -> return $ ADTVal (show $ x' >= y') Nothing
      "<=" -> evalInts >>= \(x', y') -> return $ ADTVal (show $ x' <= y') Nothing
      ">" -> evalInts >>= \(x', y') -> return $ ADTVal (show $ x' > y') Nothing
      "<" -> evalInts >>= \(x', y') -> return $ ADTVal (show $ x' < y') Nothing
      "&&" -> do
          ADTVal a Nothing <- eval c x
          ADTVal b Nothing <- eval c y
          return $ ADTVal (show $ read a && read b) Nothing
      "||" -> do
          ADTVal a Nothing <- eval c x
          ADTVal b Nothing <- eval c y
          return $ ADTVal (show $ read a || read b) Nothing
      "=>" -> do
          ADTVal a Nothing <- eval c x
          ADTVal b Nothing <- eval c y
          return $ ADTVal (show $ not (read a) || read b) Nothing
    where
        evalInts = do
            Lit (LitInt x') <- eval c x
            Lit (LitInt y') <- eval c y
            return (x', y')

-------------------------------------------------------------------------------
-- Exported Functions
-------------------------------------------------------------------------------

evalExpr :: CoreExpr -> CoreExpr
evalExpr e = fromJust $ runReaderT (eval ([], []) e) []

evalModule :: Program -> CoreExpr
evalModule p@(Program adts _ _ cbs) =
    traceShow p $ case find (\(CoreBinding n _) -> n == "main") cbs of
      Nothing -> errorWithoutStackTrace "[Eval] No main function defined."
      Just (CoreBinding _ exp) -> case runReaderT (eval ([], map (\(CoreBinding n e) -> (n, e)) cbs) exp) adts of
                                    Nothing -> error "[Eval] Evaluation failed, this shouldn't happen and might be because maybe an assertion typechecked incorrectly (haven't tried fixing this bug yet :))"
                                    Just res -> res


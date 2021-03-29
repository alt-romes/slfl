
module Eval where 

import Data.Maybe
import Prelude hiding (True,False,Bool)
import Lexer
import Syntax
import Check

type EEnv = [(Id,Expr)] -- Eval env


eval :: EEnv -> Expr -> Maybe Expr
eval _ True = return True
eval _ False = return False
eval _ UnitV = return UnitV
eval _ Zero = return Zero
eval ctxt (Succ e) = do
    r <- eval ctxt e
    return $ Succ r
eval ctxt (Abs id ty ex) = return $ Abs id ty ex
eval ctxt (Var x) = lookup x ctxt
eval ctxt (App e1 e2) = if isValue e1 == Syntax.True then
                            if isValue e2 == Syntax.True then
                                let (Abs id1 _ ex) = e1 in
                                eval ((id1,e2):ctxt) ex
                            else do
                                s <- eval ctxt e2
                                eval ctxt (App e1 s)
                        else do
                            s <- eval ctxt e1
                            eval ctxt (App s e2)

eval ctxt (If e1 e2 e3) = do
    cond <- eval ctxt e1
    if cond == Syntax.True then eval ctxt e2
    else eval ctxt e3

eval ctxt (Seqnc e1 e2) = eval ctxt e2

eval ctxt (Ascript e1 t2) = eval ctxt e1

eval ctxt (LetIn x e1 e2) = do
    r1 <- eval ctxt e1
    eval ((x, r1):ctxt) e2

eval ctxt (PairV e1 e2) = do
    r1 <- eval ctxt e1
    r2 <- eval ctxt e2
    return $ PairV r1 r2

eval ctxt (First e1) = do
    r1 <- eval ctxt e1
    case r1 of
        (PairV e2 _) -> eval ctxt e2
        _ -> Nothing
            
eval ctxt (Second e1) = do
    r1 <- eval ctxt e1
    case r1 of
        (PairV _ e2) -> eval ctxt e2
        _ -> Nothing

eval ctxt (TupleV l) =
    let valueslist = mapMaybe (eval ctxt) l in
        if length valueslist == length l then
            return $ TupleV valueslist
        else
            Nothing

eval ctxt (Project i e1) = do
    r1 <- eval ctxt e1
    case r1 of
        (TupleV l) -> return (l !! i)
        _ -> Nothing


evalTyped :: Expr -> String
evalTyped e = if isJust (check e) then
                  maybe "Eval error." show (eval [] e)
              else
                  "Type error."

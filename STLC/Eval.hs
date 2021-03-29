
module Eval where 

import Data.Maybe
import Prelude hiding (True,False,Bool)
import Syntax
import Check

type EEnv = [(Id,Expr)] -- Eval env


getAbsId :: Expr -> Id
getAbsId (Abs id _ _) = id


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
                                let (Abs _ _ ex) = e1 in
                                eval ((getAbsId e1,e2):ctxt) ex
                            else do
                                s <- eval ctxt e2
                                eval ctxt (App e1 s)
                        else do
                            s <- eval ctxt e1
                            eval ctxt (App s e2)

eval ctxt (If e1 e2 e3) = if e1 == Syntax.True then eval ctxt e2 else eval ctxt e3

evalTyped :: Expr -> String
evalTyped e = if isJust (check e) then
                  maybe "Eval error." show (eval [] e)
              else
                  "Type error."

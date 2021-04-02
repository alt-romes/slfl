
module Eval where 

import Data.Maybe
import Prelude hiding (True,False,Bool)
import Parser
import Syntax
import Check

type EEnv = [(Id,Expr)] -- Eval env


eval :: EEnv -> Expr -> Expr
eval _ True = True
eval _ False = False
eval _ UnitV = UnitV
eval _ Zero = Zero
eval ctxt (Succ e) = Succ (eval ctxt e)
eval ctxt (Abs id ty ex) = Abs id ty ex
eval ctxt (Var x) = fromJust $ lookup x ctxt
eval ctxt (App e1 e2) =
    case (eval ctxt e1, eval ctxt e2) of
      (Abs id _ e1' , v) -> eval ((id,v):ctxt) e1'

eval ctxt (If e1 e2 e3) =
    if eval ctxt e1 == Syntax.True then eval ctxt e2
    else eval ctxt e3

eval ctxt (Seqnc e1 e2) = eval ctxt e2

eval ctxt (Ascript e1 t2) = eval ctxt e1

eval ctxt (LetIn x e1 e2) =
    eval ((x, eval ctxt e1):ctxt) e2

eval ctxt (PairV e1 e2) =
    PairV (eval ctxt e1) (eval ctxt e2)

eval ctxt (First e1) =
    case eval ctxt e1 of
        (PairV e2 _) -> eval ctxt e2
        _ -> error "Isn't well typed!"
            
eval ctxt (Second e1) =
    case eval ctxt e1 of
        (PairV _ e2) -> eval ctxt e2
        _ -> error "Isn't well typed!"

eval ctxt (TupleV l) = TupleV (map (eval ctxt) l)

eval ctxt (Project i e1) =
    case eval ctxt e1 of
        (TupleV l) -> (l !! i)
        _ -> error "Isn't well typed!"


evalTyped :: Expr -> String
evalTyped e = if isJust (check e) then
                  show (eval [] e)
              else
                  "Type error."


evalP :: String -> String
evalP e = evalTyped $ parseP e

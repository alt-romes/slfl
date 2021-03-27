

module Syntax where 

import Prelude hiding (True,False,Bool)

type Id = String

data Expr 
    = Var Id -- x
    | App Expr Expr -- E1 E2
    | Abs Id Type Expr -- lambda x:T . E
    | True
    | False 
    | If Expr Expr Expr 
    | UnitV -- Unit value
    | Seqnc Expr Expr -- t1;t2, evaluate t1 to unit followed by t2 = (\x : Unit . t2) t1


-- data Values ??? (Abs Id Type Expr, UnitV)

    
data Type 
    = Fun Type Type -- T1 -> T2 
    | Bool
    | A             -- base type
    | Unit
    deriving (Eq)

instance (Show Type) where 
    show Bool = "Bool"
    show (Fun t1 t2) = "(" ++ show t1 ++ " -> " ++ show t2 ++ ")"
    show Unit = "Unit"


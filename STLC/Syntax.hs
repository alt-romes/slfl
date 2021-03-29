

module Syntax where 

import Prelude hiding (True,False,Bool)

type Id = String

data Expr 
    = Var Id -- x
    | App Expr Expr -- E1 E2
    | Abs Id Type Expr -- lambda x:T . E
    | True
    | False
    | UnitV -- Unit value
    | Zero
    | Succ Expr
    | If Expr Expr Expr 
    | Seqnc Expr Expr -- t1;t2, evaluate t1 to unit followed by t2 = (\x : Unit . t2) t1
    | Ascript Expr Type
    | LetIn Id Expr Expr
    | PairV Expr Expr -- Pair value
    | First Expr
    | Second Expr
  -- Prof tem de rever os tuples, parece-me que a minha implementação pode não ser a melhor :)
    | TupleV [Expr]
    | Project Int Expr
    deriving (Show, Eq)

isValue :: Expr -> Expr
isValue e =
    case e of
        False -> True
        True -> True
        UnitV -> True
        Zero -> True
        Succ _ -> True
        Abs {} -> True
        (PairV _ _) -> True
        TupleV _ -> True
        _ -> False


-- data Value
--     = Abs Id Type Expr
--     | True
--     | False
--     | Zero
--     | Succ Expr

    
data Type 
    = Fun Type Type -- T1 -> T2 
    | Bool
    | Nat
    | A             -- base type
    | Unit
    | Pair Type Type -- T1 x T2
    | Tuple [Type] -- T1 x T2 x T3 x T4 ...
    deriving (Eq)


instance (Show Type) where 
    show Bool = "Bool"
    show (Fun t1 t2) = "(" ++ show t1 ++ " -> " ++ show t2 ++ ")"
    show Unit = "Unit"
    show (Pair t1 t2) = "(" ++ show t1 ++ " x " ++ show t2 ++ ")"
    show (Tuple []) = "()"
    show (Tuple (x:xs)) = "( " ++ show x ++ concatMap (\x -> " x " ++ show x) xs ++ " )"
    show Nat = "Nat"


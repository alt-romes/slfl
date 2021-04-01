module Syntax where 

import Data.List
import Prelude hiding (True,False,Bool)

type Id = String

data Expr 
    = Var Id -- x
    | True
    | False
    | UnitV -- Unit value
    | Zero
    | Abs Id Type Expr -- lambda x:T . E
    | App Expr Expr -- E1 E2
    | Succ Expr
    | If Expr Expr Expr 
    | Seqnc Expr Expr -- t1;t2, evaluate t1 to unit followed by t2 = (\x : Unit . t2) t1
    | Ascript Expr Type
    | LetIn Id Expr Expr
    | PairV Expr Expr -- Pair value
    | First Expr
    | Second Expr
    | TupleV [Expr]
    | Project Int Expr
    deriving (Show, Eq)

data Type 
    = Fun Type Type -- T1 -> T2 
    | Bool
    | Nat
    | Unit
    | Pair Type Type -- T1 x T2
    | Tuple [Type] -- T1 x T2 x T3 x T4 ...
    deriving (Eq)

-- No longer used
-- isValue :: Expr -> Prelude.Bool
-- isValue e =
--     case e of
--         False -> Prelude.True
--         True -> Prelude.True
--         UnitV -> Prelude.True
--         Zero -> Prelude.True
--         Succ _ -> Prelude.True
--         Abs {} -> Prelude.True
--         (PairV _ _) -> Prelude.True
--         TupleV _ -> Prelude.True
--         _ -> Prelude.False


-- data Value
--     = Abs Id Type Expr
--     | True
--     | False
--     | Zero
--     | Succ Expr

instance (Show Type) where 
    show Bool = "Bool"
    show (Fun t1 t2) = "(" ++ show t1 ++ " -> " ++ show t2 ++ ")"
    show Unit = "Unit"
    show (Pair t1 t2) = "(" ++ show t1 ++ " x " ++ show t2 ++ ")"
    show (Tuple l) = "( " ++ intercalate " x " (map show l) ++ " )"
    show Nat = "Nat"


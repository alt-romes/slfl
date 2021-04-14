module CoreSyntax where 

import Prelude hiding (Bool)

-- References
-- https://www.microsoft.com/en-us/research/wp-content/uploads/2016/11/trees-that-grow.pdf
-- como não me repetir ao definir a sugared e desugared AST ? :)

data CoreExpr
    = BLVar Int     -- bound linear/restricted var
    | BUVar Int     -- bound unrestricted var
    -- | FVar String   -- free variable # TODO: assume free variables to be unrestricted? free variables in linear logic ??

    | Abs Type CoreExpr -- lambda x:T -> M . with Bruijn indices
    | App CoreExpr CoreExpr -- M N

    | TensorValue CoreExpr CoreExpr
    | UnitValue
    | WithValue CoreExpr CoreExpr
    | PlusValue CoreExpr CoreExpr
    | BangValue CoreExpr

    | Tru
    | Fls


data Type
    = Fun Type Type     -- A -o B 
    | Tensor Type Type  -- A * B    -- multiplicative conjunction
    | Unit              -- 1
    | With Type Type    -- A & B    -- additive conjuntion
    | Plus Type Type    -- A + B    -- additive disjunction
    | Bang Type         -- !A       -- exponential

    | Bool
    
    deriving (Eq)


instance (Show Type) where 
    show Bool = "Bool"
    show (Fun t1 t2) = "(" ++ show t1 ++ " -o " ++ show t2 ++ ")"

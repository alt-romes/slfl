module CoreSyntax where 

import Prelude hiding (Bool)


data CoreExpr

    = BLVar Int             -- bound linear/restricted var
    | BUVar Int             -- bound unrestricted var
    -- TODO: assume free variables to be unrestricted? free variables in linear logic ??
    -- | FVar String        -- free variable 

    -- A -o B
    | Abs Type CoreExpr     -- \x:T -> M . with Bruijn indices
    | App CoreExpr CoreExpr -- M N

    -- A (*) B
    | TensorValue CoreExpr CoreExpr
    | LetTensor String String CoreExpr CoreExpr

    -- 1
    | UnitValue
    | LetUnit CoreExpr CoreExpr

    -- A & B
    | WithValue CoreExpr CoreExpr
    | Fst CoreExpr
    | Snd CoreExpr

    -- A (+) B
    | InjL Type CoreExpr    -- inr:A M : A (+) typeof M
    | InjR Type CoreExpr    -- inl:B M : typeof M (+) A
    | CaseOfPlus CoreExpr String CoreExpr String CoreExpr -- case M of inl x => N | inr y => P : C

    -- !A
    | BangValue CoreExpr
    | LetBang CoreExpr CoreExpr

    -- Non-canonical

    -- Bool
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
    show (Fun t1 t2) = "(" ++ show t1 ++ " -o " ++ show t2 ++ ")"
    show (Tensor t1 t2) = show t1 ++ " (*) " ++ show t2
    show Unit = "1"
    show (With t1 t2) = show t1 ++ " (&) " ++ show t2
    show (Plus t1 t2) = show t1 ++ " (+) " ++ show t2
    show (Bang t1) = "!" ++ show t1
    show Bool = "Bool"

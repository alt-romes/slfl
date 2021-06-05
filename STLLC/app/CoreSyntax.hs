module CoreSyntax where 

import Prelude hiding (Bool)
import Control.Monad
import qualified Data.Map as Map

type Name = String


data CoreBinding = CoreBinding Name CoreExpr
instance (Show CoreBinding) where
    show (CoreBinding s e) = s ++ ":\n" ++ show e ++ "\n"

data CoreExpr

    = BLVar Int             -- bound linear/restricted var
    | BUVar Int             -- bound unrestricted var
    | FLVar String          -- free linear/restricted var
    | FUVar String          -- free unrestricted var

    -- A -o B
    | Abs (Maybe Type) CoreExpr     -- \x:T -> M . with Bruijn indices
    | App CoreExpr CoreExpr -- M N

    -- A (*) B
    | TensorValue CoreExpr CoreExpr
    | LetTensor CoreExpr CoreExpr

    -- 1
    | UnitValue
    | LetUnit CoreExpr CoreExpr

    -- A & B
    | WithValue CoreExpr CoreExpr
    | Fst CoreExpr
    | Snd CoreExpr

    -- A (+) B
    | InjL (Maybe Type) CoreExpr    -- inr A : M has type A (+) typeof M
    | InjR (Maybe Type) CoreExpr    -- inl M : B has type typeof M (+) A
    | CaseOfPlus CoreExpr CoreExpr CoreExpr -- case M of inl x => N | inr y => P : C

    -- !A
    | BangValue CoreExpr
    | LetBang CoreExpr CoreExpr

    -- Non-canonical

    | LetIn CoreExpr CoreExpr

    | Mark Int [(String, Scheme)] (Maybe Type)

    -- Bool
    | Tru
    | Fls
    | IfThenElse CoreExpr CoreExpr CoreExpr

    -- Sum types
    | SumValue [(String, Maybe Type)] (String, CoreExpr)
    | CaseOfSum CoreExpr [(String, CoreExpr)]

    deriving (Eq)


data Type
    = Fun Type Type     -- A -o B 
    | Tensor Type Type  -- A * B    -- multiplicative conjunction
    | Unit              -- 1
    | With Type Type    -- A & B    -- additive conjuntion
    | Plus Type Type    -- A + B    -- additive disjunction
    | Bang Type         -- !A       -- exponential

    | TypeVar Int       -- Type variable (uninterpreted type) used for reconstruction
    | ExistentialTypeVar Int

    | Bool
    
    | Atom String

    | Sum [(String, Type)] -- TODO: Os Sum Type deviam ter as labels também ? 

    | ADT String
    
    deriving (Eq)

data Scheme = Forall [Int] Type 
    deriving (Eq)

instance (Show Type) where 
    show (Fun t1 t2) = "(" ++ show t1 ++ " -o " ++ show t2 ++ ")"
    show (Tensor t1 t2) = "(" ++ show t1 ++ " * " ++ show t2 ++ ")"
    show Unit = "1"
    show (With t1 t2) = "(" ++ show t1 ++ " & " ++ show t2 ++ ")"
    show (Plus t1 t2) = "(" ++ show t1 ++ " + " ++ show t2 ++ ")"
    show (Bang t1) = "(! " ++ show t1 ++ ")"
    show Bool = "Bool"
    show (Atom x) = x
    show (TypeVar x) = letters !! x
    show (ExistentialTypeVar x) = "?" ++ letters !! x
    show (Sum ts) = "+ { " ++ foldl (\p (s, t) -> p ++ s ++ " : " ++ show t ++ "; ") "" ts ++ "}"
    show (ADT t) = t

instance (Show Scheme) where
    show (Forall ns t) = (if null ns then "" else foldl (\p n -> p ++ " " ++ (letters !! n)) "forall" ns ++ ". ") ++ show t

instance (Show CoreExpr) where
    show e = showexpr' 0 e

showexpr' :: Int -> CoreExpr -> String -- Use Int (depth) to indent the code
showexpr' d (BLVar x) = "BL(" ++ show x ++ ")"
showexpr' d (BUVar x) = "BU(" ++ show x ++ ")"
showexpr' d (FLVar x) = "FL(" ++ show x ++ ")"
showexpr' d (FUVar x) = "FU(" ++ show x ++ ")"
showexpr' d (Abs t e) = indent d ++ "(λ" ++ " : " ++ show t ++ " -> " ++ showexpr' (d+1) e ++ ")"
showexpr' d (App e1 e2) = showexpr' d e1 ++ " " ++ showexpr' d e2
showexpr' d (TensorValue e1 e2) = "< " ++ showexpr' d e1 ++ " * " ++ showexpr' d e2 ++ " >"
showexpr' d (LetTensor e1 e2) = indent d ++ "let " ++ "?" ++ "*" ++ "?" ++ " = " ++ showexpr' d e1 ++ " in " ++ showexpr' (d+1) e2
showexpr' d UnitValue = "<>"
showexpr' d (LetUnit e1 e2) = indent d ++ "let _ = " ++ showexpr' d e1 ++ " in " ++ showexpr' (d+1) e2
showexpr' d (WithValue e1 e2) = "< " ++ showexpr' d e1 ++ " & " ++ showexpr' d e2 ++ " >"
showexpr' d (Fst a@(App _ _)) = "fst (" ++ showexpr' d a ++ ")"
showexpr' d (Snd a@(App _ _)) = "snd (" ++ showexpr' d a ++ ")"
showexpr' d (Fst e) = "fst " ++ showexpr' d e
showexpr' d (Snd e) = "snd " ++ showexpr' d e
showexpr' d (InjL t e) = "inl " ++ showexpr' d e ++ " : " ++ show t
showexpr' d (InjR t e) = "inr " ++ show t ++ " : " ++ showexpr' d e
showexpr' d (CaseOfPlus e1 e2 e3) = indent d ++ "case " ++ showexpr' d e1 ++ " of " ++
                                            indent (d+1) ++ "inl " ++ "?" ++ " => " ++ showexpr' (d+2) e2 ++
                                            indent (d+1) ++ "| inr " ++ "?" ++ " => " ++ showexpr' (d+2) e3
showexpr' d (BangValue e) = "! " ++ showexpr' d e ++ ""
showexpr' d (LetBang e1 e2) = indent d ++ "let !" ++ "?" ++ " = " ++ showexpr' d e1 ++ " in " ++ showexpr' (d+1) e2
showexpr' d (LetIn e1 e2) = indent d ++ "let " ++ "?" ++ " = " ++ showexpr' d e1 ++ " in " ++ showexpr' (d+1) e2
showexpr' d (Mark _ _ t) = "{{ " ++ show t ++ " }}"
showexpr' d (IfThenElse e1 e2 e3) = indent d ++ "if " ++ showexpr' d e1 ++ 
                                        indent (d+1) ++ "then " ++ showexpr' (d+1) e2 ++
                                        indent (d+1) ++ "else " ++ showexpr' (d+1) e3
showexpr' d Tru = "true"
showexpr' d Fls = "false"
showexpr' d (SumValue mts (s, e)) = indent d ++ "union {" ++
    foldl (\p (s, Just t) -> p ++ indent (d+2) ++ s ++ " : " ++ show t ++ ";") "" mts
    ++ indent (d+2) ++ s ++ " " ++ show e ++ ";"
    ++ indent (d+1) ++ "}"
showexpr' d (CaseOfSum e ((tag, e1):exps)) = indent d ++ "case " ++ showexpr' d e ++ " of " ++
    indent (d+1) ++ "  " ++ tag ++ " " ++ "?" ++ " => " ++ showexpr' (d+2) e1 ++
        foldl (\p (t, ex) -> p ++ indent (d+1) ++ 
            "| " ++ t ++ " " ++ "?" ++ " => " ++
                showexpr' (d+2) ex) "" exps
indent d = (if d == 0 then "" else "\n") ++ replicate (4*d) ' '


---- Util

letters :: [String]
letters = [1..] >>= flip replicateM ['a'..'z']

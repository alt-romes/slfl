module Syntax where 

import Prelude hiding (Bool)
import CoreSyntax (Type)

type Binding = (String, Expr)

data Expr

    = Var String

    -- A -o B
    | Abs String Type Expr     -- \x:T -> M . with Bruijn indices
    | App Expr Expr     -- M N

    -- A (*) B
    | TensorValue Expr Expr
    | LetTensor String String Expr Expr

    -- 1
    | UnitValue
    | LetUnit Expr Expr

    -- A & B
    | WithValue Expr Expr
    | Fst Expr
    | Snd Expr

    -- A (+) B
    | InjL Type Expr    -- inl:B M : typeof M (+) A
    | InjR Type Expr    -- inr:A M : A (+) typeof M
    | CaseOfPlus Expr String Expr String Expr -- case M of inl x => N | inr y => P : C

    -- !A
    | BangValue Expr
    | LetBang String Expr Expr

    -- Non-canonical

    | IfThenElse Expr Expr Expr

    -- Bool
    | Tru
    | Fls

    -- Added sugar :)
    | LetIn String Expr Expr


data Pattern
    = TensorPattern String String
    | UnitPattern
    | BangPattern String
    
    | VanillaPattern String


instance (Show Expr) where
    show (Var x) = x

    show (Abs x t e) = "λ" ++ x ++ " : " ++ show t ++ " -> " ++ show e
    show (App e1 e2) = show e1 ++ " " ++ show e2

    show (TensorValue e1 e2) = "< " ++ show e1 ++ " * " ++ show e2 ++ " >"
    show (LetTensor u v e1 e2) = "let " ++ u ++ "*" ++ v ++ " = " ++ show e1 ++ " in " ++ show e2

    show UnitValue = "<>"
    show (LetUnit e1 e2) = "let _ = " ++ show e1 ++ " in " ++ show e2

    show (WithValue e1 e2) = "< " ++ show e1 ++ " & " ++ show e2 ++ " >"
    show (Fst e) = "fst " ++ show e
    show (Snd e) = "snd " ++ show e

    show (InjL t e) = "inl:" ++ show t ++ " " ++ show e
    show (InjR t e) = "inr:" ++ show t ++ " " ++ show e
    show (CaseOfPlus e1 x e2 y e3) = "case " ++ show e1 ++ " of inl " ++ x ++ " -> " ++ show e2 ++ " | inr " ++ y ++ " -> " ++ show e3

    show (BangValue e) = "!" ++ show e
    show (LetBang x e1 e2) = "let !" ++ x ++ " = " ++ show e1 ++ " in " ++ show e2

    show (IfThenElse e1 e2 e3) = "if " ++ show e1 ++ " then " ++ show e2 ++ " else " ++ show e3
    show Tru = "true"
    show Fls = "false"

    show (LetIn x e1 e2) = "let " ++ x ++ " = " ++ show e1 ++ " in " ++ show e2
    

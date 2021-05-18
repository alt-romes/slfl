module Syntax where 

import Prelude hiding (Bool)
import CoreSyntax (Type)

data Binding = Binding String Expr
instance (Show Binding) where
    show (Binding s e) = "\nlet " ++ s ++ " =\n" ++ show e

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

    | TypedPlaceholder Type

data Pattern
    = TensorPattern String String
    | UnitPattern
    | BangPattern String
    
    | VanillaPattern String

-- showexpr :: Expr -> String
-- showexpr = showexpr' 0
instance (Show Expr) where
    show t = showexpr' 0 t

showexpr' :: Int -> Expr -> String -- Use Int (depth) to indent the code
showexpr' d (Var x) = x

showexpr' d (Abs x t e) = indent d ++ "(λ" ++ x ++ " : " ++ show t ++ " -> " ++ showexpr' (d+1) e ++ ")"
showexpr' d (App e1 e2) = showexpr' d e1 ++ " " ++ showexpr' d e2

showexpr' d (TensorValue e1 e2) = "< " ++ showexpr' d e1 ++ " * " ++ showexpr' d e2 ++ " >"
showexpr' d (LetTensor u v e1 e2) = indent d ++ "let " ++ u ++ "*" ++ v ++ " = " ++ showexpr' d e1 ++ " in " ++ showexpr' (d+1) e2

showexpr' d UnitValue = "<>"
showexpr' d (LetUnit e1 e2) = indent d ++ "let _ = " ++ showexpr' d e1 ++ " in " ++ showexpr' (d+1) e2

showexpr' d (WithValue e1 e2) = "< " ++ showexpr' d e1 ++ " & " ++ showexpr' d e2 ++ " >"
showexpr' d (Fst a@(App _ _)) = "fst (" ++ showexpr' d a ++ ")"
showexpr' d (Snd a@(App _ _)) = "snd (" ++ showexpr' d a ++ ")"
showexpr' d (Fst e) = "fst " ++ showexpr' d e
showexpr' d (Snd e) = "snd " ++ showexpr' d e

showexpr' d (InjL t e) = "inl " ++ showexpr' d e ++ " : " ++ show t
showexpr' d (InjR t e) = "inr " ++ show t ++ " : " ++ showexpr' d e
showexpr' d (CaseOfPlus e1 x e2 y e3) = indent d ++ "case " ++ showexpr' d e1 ++ " of " ++
                                            indent (d+1) ++ "inl " ++ x ++ " => " ++ showexpr' (d+2) e2 ++
                                            indent (d+1) ++ "| inr " ++ y ++ " => " ++ showexpr' (d+2) e3

showexpr' d (BangValue e) = "! " ++ showexpr' d e ++ ""
showexpr' d (LetBang x e1 e2) = indent d ++ "let !" ++ x ++ " = " ++ showexpr' d e1 ++ " in " ++ showexpr' (d+1) e2

showexpr' d (IfThenElse e1 e2 e3) = indent d ++ "if " ++ showexpr' d e1 ++ 
                                        indent (d+1) ++ "then " ++ showexpr' (d+1) e2 ++
                                        indent (d+1) ++ "else " ++ showexpr' (d+1) e3
showexpr' d Tru = "true"
showexpr' d Fls = "false"

showexpr' d (LetIn x e1 e2) = indent d ++ "let " ++ x ++ " = " ++ showexpr' d e1 ++ " in " ++ showexpr' (d+1) e2

showexpr' d (TypedPlaceholder t) = "{{ " ++ show t ++ " }}"

indent d = (if d == 0 then "" else "\n") ++ replicate (4*d) ' '

module Syntax where 

import Prelude hiding (Bool)
import CoreSyntax

-- References
-- https://www.microsoft.com/en-us/research/wp-content/uploads/2016/11/trees-that-grow.pdf
-- como não me repetir ao definir a sugared e desugared AST ? :)

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
    | InjL Type Expr    -- inr:A M : A (+) typeof M
    | InjR Type Expr    -- inl:B M : typeof M (+) A
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

    deriving (Show)


data Pattern
    = TensorPattern String String
    | UnitPattern
    | BangPattern String
    
    | VanillaPattern String

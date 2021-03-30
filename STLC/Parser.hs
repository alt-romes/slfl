module Parser where

import Prelude hiding (True,False,Bool)
import Lexer
import Syntax

parse :: [Token] -> Maybe (Expr, [Token])

parse ("true":xs) = return (True, xs)
parse ("false":xs) = return (False, xs)
parse ("0":xs) = return (Zero, xs)
parse ("succ":xs) = do
    (e1, xs1) <- parse xs
    return (Succ e1, xs1)
parse ("if":xs) = do
    (e1, "then":xs1) <- parse xs
    (e2, "else":xs2) <- parse xs1
    (e3, xs3) <- parse xs2
    return (If e1 e2 e3, xs3)
parse ("x":xs) = return (Var "x", xs)
parse ("y":xs) = return (Var "y", xs)
parse ("z":xs) = return (Var "z", xs)
parse ("->":xs) = parse xs
parse ("lambda":xs) =
    let (id:xs1) = xs in do
    (t1, xs2) <- parseType xs1
    (e1, xs3) <- parse xs2
    return (Abs id t1 e1, xs3)
parse ("!->":xs) = do
    (e1, xs1) <- parse xs
    (e2, xs2) <- parse xs1
    return (App e1 e2, xs2)
parse ("unit":xs) = return (UnitV, xs)
parse (";->":xs) = do
    (e1, xs1) <- parse xs
    (e2, xs2) <- parse xs1
    return (Seqnc e1 e2, xs2)
parse (".":xs) = parse xs
parse ("let":xs) = 
    let (id:("=":xs1)) = xs in do
    (e1, "in":xs2) <- parse xs1
    (e2, xs3) <- parse xs2
    return (LetIn id e1 e2, xs3)


parseType :: [Token] -> Maybe (Type, [Token])
parseType (":":xs) = parseType xs
parseType ("Bool":xs) = return (Bool, xs)
parseType ("Nat":xs) = return (Nat, xs)


parseP :: String -> Expr
parseP s = maybe (error "Parsing error") fst (parse (lexer s))

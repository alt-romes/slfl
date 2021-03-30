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
parse ("then":xs) = parse xs
parse ("else":xs) = parse xs
parse ("if":xs) = do
    (e1, xs1) <- parse xs
    if head xs1 == "then" then do
        (e2, xs2) <- parse xs1
        if head xs2 == "else" then do
            (e3, xs3) <- parse xs2
            return (If e1 e2 e3, xs3)
        else
            Nothing
    else
        Nothing
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


parseType :: [Token] -> Maybe (Type, [Token])
parseType (":":xs) = parseType xs
parseType ("Bool":xs) = return (Bool, xs)
parseType ("Nat":xs) = return (Nat, xs)


parseP :: String -> Expr
parseP s = maybe (error "Parsing error") fst (parse (lexer s))

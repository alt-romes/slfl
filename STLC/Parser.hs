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

parseP :: String -> Expr
parseP s = maybe (error "Parsing error") fst (parse (lexer s))

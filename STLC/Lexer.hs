
module Lexer where 

-- data Token
--     = True
--     | False
--     | Zero
--     | Succ
--     | Var String
--     | If
--     | Then
--     | Else
--     | OpenBrace -- `{`
--     | CloseBrace -- `}`
--     | Dot
--     deriving (Show, Eq)

type Token = String

validTokens = ["true", "false", "0", "if", "then", "else", "x", "y", "z", "succ", "lambda", "Bool", "Nat", "->", ":", "(", ")", "!->", "unit", ";->", ".", "let", "in", "=", "-->"]

lexer :: String -> [Token]

lexer s = filter (`elem` validTokens) (words s)


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

validTokens = ["True", "False", "Zero", "if", "then", "else", "x", "y", "z", "succ"]

lexer :: String -> [Token]

lexer s = filter (`elem` validTokens) (words s)

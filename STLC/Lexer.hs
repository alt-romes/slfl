
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

lexer :: String -> [Token]

lexer = words

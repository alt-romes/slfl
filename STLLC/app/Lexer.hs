module Lexer where

import Text.Parsec
import Text.Parsec.String
import qualified Text.Parsec.Token as Tok
import Text.Parsec.Language

lexer :: Tok.TokenParser ()
lexer = Tok.makeTokenParser style
  where ops = ["\\", "λ", ":", "->", "*", "=", "&", "=>", "|", "-o", "&", "+", "1", "Bool", "!"]
        names = ["true", "false", "let", "in", "fst", "snd", "inl", "inr", "case", "of", "if", "then", "else", "_"]
        style = haskellStyle {Tok.reservedOpNames = ops,
                              Tok.reservedNames = names,
                              Tok.commentLine = "#"}

reserved :: String -> Parser ()
reserved = Tok.reserved lexer

reservedOp :: String -> Parser ()
reservedOp = Tok.reservedOp lexer

identifier :: Parser String
identifier = Tok.identifier lexer

natural :: Parser Integer
natural = Tok.natural lexer

parens :: Parser a -> Parser a
parens = Tok.parens lexer

contents :: Parser a -> Parser a
contents p = do
  Tok.whiteSpace lexer
  r <- p
  eof
  return r

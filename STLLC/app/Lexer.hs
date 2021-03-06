module Lexer where

import Text.Parsec
import qualified Text.Parsec.Token as Tok
import Text.Parsec.Language



type Parser = Parsec String Int

-------------------------------------------------------------------------------
-- Functions
-------------------------------------------------------------------------------

lexer :: Tok.TokenParser Int
lexer = Tok.makeTokenParser style
  where ops = ["\\", "λ", ":", "->", "*", "=", "&", "=>", "|", "-o", "&", "+", "1", "Bool", "!", "..."]
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

dot :: Parser String
dot = Tok.dot lexer

contents :: Parser a -> Parser a
contents p = do
  Tok.whiteSpace lexer
  r <- p
  eof
  return r

symbol :: String -> Parser String
symbol = Tok.symbol lexer

module Parser where

import Prelude hiding (True,False,Bool)
import Syntax

import Text.Parsec
import Data.List (elemIndex)
import Data.Either

-- References:
-- https://mattwetmore.me/posts/parsing-combinators-with-parser-combinators

type BoundContext = [String] -- Use for 
type Parser = Parsec String BoundContext Expr
-- Para os tipos não preciso de user state, o que ponho aqui na definição de tipo? Pus ao calhas, porque não interessa e wildcard não funciona...
type TypeParser = Parsec String BoundContext Type

parseName :: Parsec String u String
parseName = many1 letter

-- parseFunc :: TypeParser
-- parseFunc = do


parseBool :: TypeParser
parseBool = do
    string "Bool"
    return Bool

parseNat :: TypeParser
parseNat = do
    string "Nat"
    return Bool

parseType :: TypeParser
parseType = 
        -- parseFunc <|>
        parseBool <|> parseNat

-- Foi o LSP que sugeriu esta syntax, não a percebi completamente
parseVar :: Parser
parseVar = Var <$> parseName

-- "Usar" quando passar a *locally nameless*
-- parseVar :: Parser
-- parseVar = do
--     v <- parseName
--     list <- getState
--     findVar v list
-- findVar :: String -> BoundContext -> Parser
-- findVar v list =
--     case elemIndex v list of
--         Nothing -> fail $ "Variable " ++ v ++ " not bound"
--         Just n -> return $ BVar n -- n is "distance in lambdas from bound lambda" or something similar

parseAbs :: Parser
parseAbs = do
    char 'λ'
    v <- parseName
    space
    string "of"
    space
    t <- parseType
    modifyState (v :) -- modifies user state of parser (BoundContext) to add the bound variable
    space
    string "->"
    space
    term <- parseExpr
    modifyState tail  -- modifies user state of parser to remove the bound variable
    return $ Abs v t term

parens :: Parsec String u a -> Parsec String u a
parens = between (char '(') (char ')')

parseNonApp :: Parser
parseNonApp = parens parseExpr -- (M)
           <|> parseAbs        -- λx.M
           <|> parseVar        -- x

-- Pedir walkthrough do prof
parseExpr :: Parser
parseExpr = chainl1 parseNonApp $ do
              space
              return App

-- parseP :: String -> Either ParseError Expr
parseP :: String -> Expr
parseP s = fromRight (error "Parsing error") $ runParser parseExpr [] "untyped lambda-calculus" s

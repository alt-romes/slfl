module Parser where

import Prelude hiding (True,False,Bool)
import Syntax

import Text.Parsec
import Data.List (elemIndex)
import Data.Either

-- References:
-- https://mattwetmore.me/posts/parsing-combinators-with-parser-combinators

type BoundContext = [String] -- Use for 



--- Types

-- Para os tipos não preciso de user state, o que ponho aqui na definição de tipo? Pus ao calhas, porque não interessa e wildcard não funciona...
type TypeParser = Parsec String BoundContext Type

parseName :: Parsec String u String
parseName = many1 letter

-- parseTypeFunc :: TypeParser
-- parseTypeFunc = do

parseTypeBool :: TypeParser
parseTypeBool = do
    string "Bool"
    return Bool

parseTypeNat :: TypeParser
parseTypeNat = do
    string "Nat"
    return Bool

parseType :: TypeParser
parseType = 
        -- parseFunc <|>
        parseTypeBool <|> parseTypeNat



--- Expressions

type Parser = Parsec String BoundContext Expr

parens :: Parsec String u a -> Parsec String u a
parens = between (char '(') (char ')')

ignoreReserved :: Parsec String BoundContext String
ignoreReserved =  string "then"

reservedWords = ["then", "else"]

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
    char ':'
    space
    t <- parseType
    modifyState (v :) -- modifies user state of parser (BoundContext) to add the bound variable
    space
    string "->"
    space
    term <- parseExpr
    modifyState tail  -- modifies user state of parser to remove the bound variable
    return $ Abs v t term

-- Isto parece ter um problema, como "True" tem prioridade sobre Var "True", não dá para escrever
-- variáveis com letra grande a começar com T (etc...) porque ele está à espera de True
parseConstant :: Parser
parseConstant =  do {string "true"; return True}
             <|> do {string "false"; return False}
             <|> do {string "0"; return Zero}
             <|> do {string "()"; return UnitV}


parseIf :: Parser
parseIf = do
    string "if"
    space
    e1 <- parseExpr
    space
    string "then"
    space
    e2 <- parseExpr
    space
    string "else"
    space
    If e1 e2 <$> parseExpr

parseNonApp :: Parser
parseNonApp =  parens parseExpr -- (M)
           <|> parseAbs        -- λx.M
           <|> parseConstant   -- constants
           <|> parseIf         -- if expr then expr else epxr
           <|> parseVar        -- x

-- Pedir walkthrough do prof
-- edit2: passei horas a tentar fazer com que o chainl1 não "comesse" o espaço para o "then" e o "else"
-- e retornar uma expressão App True (Var "then"), e os notFollowedBy não estavam a funcionar nenhuma das vezes até
-- eu por o "try" antes do `do` block. O prof depois tem de ver isto melhor comigo
parseExpr :: Parser
parseExpr = chainl1 parseNonApp $ try $ do
                space
                notFollowedBy $ string "then" -- seria bom ter um array de reserved words, em vez disto
                notFollowedBy $ string "else"
                return App
               -- Need a way to parse reserved words first to make sure something like:
               -- "if" construct (or else if True then ...) isn't an (App True (Var "then") ...)

parsePE :: String -> Either ParseError Expr
parsePE = runParser parseExpr [] "untyped lambda-calculus"

-- parseP :: String -> Either ParseError Expr
parseP :: String -> Expr
parseP s = fromRight (error "Parsing error") $ runParser parseExpr [] "untyped lambda-calculus" s

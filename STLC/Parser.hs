module Parser where

import Prelude hiding (True,False,Bool)

import Lexer
import Syntax

import Text.Parsec
import Text.Parsec.String 
import qualified Text.Parsec.Expr as Ex 

-- import Data.List (elemIndex)
-- import Data.Either

-- type BoundContext = [String] -- Use for 



-- --- Types

-- -- Para os tipos não preciso de user state, o que ponho aqui na definição de tipo? Pus ao calhas, porque não interessa e wildcard não funciona...
-- type TypeParser = Parsec String BoundContext Type

-- parseName :: Parsec String u String
-- parseName = many1 letter

-- -- parseTypeFunc :: TypeParser
-- -- parseTypeFunc = do

-- parseTypeBool :: TypeParser
-- parseTypeBool = do
--     string "Bool"
--     return Bool

-- parseTypeNat :: TypeParser
-- parseTypeNat = do
--     string "Nat"
--     return Bool

-- parseType :: TypeParser
-- parseType = 
--         -- parseFunc <|>
--         parseTypeBool <|> parseTypeNat



-- --- Expressions

-- -- type Parser = Parsec String BoundContext Expr

-- -- parens :: Parsec String u a -> Parsec String u a
-- -- parens = between (char '(') (char ')')

-- -- "Usar" quando passar a *locally nameless*
-- parseVar :: Parser
-- parseVar = do
--     v <- parseName
--     list <- getState
--     findVar v list
-- findVar :: String -> BoundContext -> Parser
-- findVar v list =
--     case elemIndex v list of
--     -- Foi o LSP que sugeriu esta syntax (<$>), não a percebi completamente (percebi o que substitui :))
--         Just n -> return $ BVar n -- n is "distance in lambdas from bound lambda" or something similar
--         Nothing -> return $ FVar v

-- parseAbs :: Parser
-- parseAbs = do
--     char 'λ' <|> char '\\'
--     v <- parseName
--     space
--     char ':'
--     space
--     t <- parseType
--     modifyState (v :) -- modifies user state of parser (BoundContext) to add the bound variable
--     space
--     string "->"
--     space
--     term <- parseExpr
--     modifyState tail  -- modifies user state of parser to remove the bound variable
--     return $ Abs t term

-- parseConstant :: Parser
-- parseConstant =  try $ do {string "true"; return True}
--              <|> do {string "false"; return False}
--              <|> do {string "0"; return Zero}
--              <|> do {string "()"; return UnitV}

-- parseIf :: Parser
-- parseIf = do
--     string "if"
--     space
--     e1 <- parseExpr
--     space
--     string "then"
--     space
--     e2 <- parseExpr
--     space
--     string "else"
--     space
--     If e1 e2 <$> parseExpr

-- parseNonApp :: Parser
-- parseNonApp =  parseConstant    -- constants
--            <|> parens parseExpr -- (M)
--            <|> parseAbs         -- λx.M
--            <|> parseIf          -- if expr then expr else epxr
--            <|> parseVar    -- bound var (w Bruijn index)



-- Parsing Expressions



unit :: Parser Expr 
unit = reserved "()" >> return UnitV

pair :: Parser Expr 
pair = do 
    reserved "("
    e1 <- expr 
    reservedOp ","
    e2 <- expr 
    reserved ")"
    return $ PairV e1 e2 

proj :: Parser Expr 
proj = 
    do 
    reserved "fst"
    First <$> expr
    <|>
    do 
    reserved "snd"
    Second <$> expr

variable :: Parser Expr 
variable = FVar <$> identifier

num :: Parser Expr 
num =
    (reserved "Z" >> return Zero)
    <|> do 
        reserved "succ"
        Succ <$> expr

isZero :: Parser Expr 
isZero = do
    reserved "isZero"
    IsZero <$> expr

bool :: Parser Expr 
bool =  (reserved "True" >> return True)
    <|> (reserved "False" >> return False)
    <|> isZero 

lambda :: Parser Expr 
lambda = do 
    reservedOp "\\"
    x <- identifier
    reservedOp ":"
    t <- type' 
    reservedOp "."
    AbsN x t <$> expr

ite :: Parser Expr 
ite = do
    reserved "if"
    cond <- expr 
    reservedOp "then"
    tr <- expr 
    reserved "else"
    If cond tr <$> expr

aexp :: Parser Expr 
aexp = parens expr 
     <|> ite 
     <|> lambda 
     <|> bool 
     <|> isZero
     <|> num 
     <|> variable
     <|> proj 
     <|> pair 
     <|> unit 

expr :: Parser Expr 
expr = aexp >>= \x -> 
-- acho que percebi bem :), o many1 vai passar pelo sequenciador
-- uma lista de expressões que vão ser associadas à esquerda uma a uma
-- pelo fold ao x e sendo assim "Acumuladas" 
-- para no final retornar a AST
             (many1 aexp >>= \xs -> return (foldl App x xs))
             <|> return x


-- Parsing Types 

ty :: Parser Type 
ty = tylit <|> parens type'

tylit :: Parser Type 
tylit =     (reservedOp "Bool" >> return Bool)
        <|> (reservedOp "Nat"  >> return Nat )
        <|> (reservedOp "Unit" >> return Unit)

-- prof só tenho a dizer ...---...
type' :: Parser Type 
type' = Ex.buildExpressionParser tyops ty
    where 
        infixOp x f = Ex.Infix (reservedOp x >> return f)
        tyops = [ 
            [infixOp "->" Fun Ex.AssocRight, infixOp "," Pair Ex.AssocLeft]
                ]


-- Toplevel

parseExpr :: String -> Either ParseError Expr
parseExpr = parse (contents expr) "<stdin>"

-- parsePE :: String -> Either ParseError Expr
-- parsePE = runParser parseExpr [] "untyped lambda-calculus"

-- parseP :: String -> Expr
-- parseP s = fromRight (error "Parsing error") $ runParser parseExpr [] "untyped lambda-calculus" s


module Parser where

import Prelude hiding (Bool)

import Lexer
import CoreSyntax
import Syntax

import Text.Parsec
import Text.Parsec.String 
import qualified Text.Parsec.Expr as Ex 

import Debug.Trace

-- Parsing Expressions

variable :: Parser Expr 
variable = Var <$> identifier

-- A -o B
lambda :: Parser Expr 
lambda = do 
    reservedOp "\\" <|> reservedOp "λ"
    x <- identifier
    reservedOp ":"
    t <- type' 
    reservedOp "->"
    Syntax.Abs x t <$> expr

-- A (*) B
tensor :: Parser Expr
tensor = do
    reservedOp "<"
    e1 <- expr
    reservedOp "*"
    e2 <- expr
    reservedOp ">"
    return $ Syntax.TensorValue e1 e2 

lettensorpattern :: Parser Pattern
lettensorpattern = do
    i1 <- identifier
    reservedOp "*"
    TensorPattern i1 <$> identifier

-- 1
unit :: Parser Expr 
unit = reserved "<>" >> return Syntax.UnitValue -- TODO : <<><*><>> breaks...

letunitpattern :: Parser Pattern
letunitpattern = do
    reserved "_"
    return UnitPattern

-- A & B
with :: Parser Expr 
with = do 
    reservedOp "<"
    e1 <- expr 
    reservedOp "&"
    e2 <- expr
    reservedOp ">"
    return $ Syntax.WithValue e1 e2

proj :: Parser Expr 
proj = 
    do 
    reserved "fst"
    Syntax.Fst <$> expr
    <|>
    do 
    reserved "snd"
    Syntax.Snd <$> expr

-- A (+) B
plus :: Parser Expr
plus =
    -- TODO: How to merge into 1 do block?
    do
    reserved "inl"
    e1 <- expr
    reservedOp ":"
    t1 <- type'
    return $ Syntax.InjL t1 e1
    <|> 
    do
    reserved "inr"
    t1 <- type'
    reservedOp ":"
    Syntax.InjR t1 <$> expr

caseplus = do
    reserved "case"
    e1 <- expr
    reserved "of"
    reserved "inl"
    i1 <- identifier
    reservedOp "=>"
    e2 <- expr
    reservedOp "|"
    reserved "inr"
    i2 <- identifier
    reservedOp "=>"
    Syntax.CaseOfPlus e1 i1 e2 i2 <$> expr

-- !A
bang :: Parser Expr
bang = do
    reservedOp "!"
    Syntax.BangValue <$> expr

letbangpattern :: Parser Pattern
letbangpattern = do
    reservedOp "!"
    BangPattern <$> identifier

-- Bool
bool :: Parser Expr 
bool = (reserved "True" >> return Syntax.Tru)
   <|> (reserved "False" >> return Syntax.Fls)
    -- <|> isZero 

letexp :: Parser Expr
letexp = do
    reserved "let"
    pat <- letpattern
    reserved "="
    e1 <- expr
    reserved "in"
    e2 <- expr
    case pat of
        TensorPattern i1 i2 -> return $ Syntax.LetTensor i1 i2 e1 e2
        UnitPattern -> return $ Syntax.LetUnit e1 e2
        BangPattern i1 -> return $ Syntax.LetBang i1 e1 e2
        VanillaPattern i1 -> return $ Syntax.LetIn i1 e1 e2

letpattern :: Parser Pattern
letpattern = do
    try lettensorpattern <|> try letunitpattern <|> try letbangpattern <|> letinpattern

-- if M then N else P
ite :: Parser Expr 
ite = do
    reserved "if"
    cond <- expr 
    reserved "then"
    tr <- expr 
    reserved "else"
    Syntax.IfThenElse cond tr <$> expr


-- Parsing sugar expressions

-- let x = M in N
letinpattern :: Parser Pattern
letinpattern = VanillaPattern <$> identifier


-- num :: Parser Expr 
-- num =
--     (reserved "Z" >> return Zero)
--     <|> do 
--         reserved "succ"
--         Succ <$> expr

-- isZero :: Parser Expr 
-- isZero = do
--     reserved "isZero"
--     IsZero <$> expr



aexp :: Parser Expr 
aexp =   parens expr 

     <|> lambda 

     <|> try tensor -- try tensor because "with" is also between "< >"... looks unclear - seria melhor outra opção :)

     <|> unit -- not correctly parsing <<>*<>>

     <|> with
     <|> proj

     <|> plus
     <|> caseplus

     <|> bang

     <|> letexp

     <|> bool 

     <|> ite 

     <|> variable

     -- <|> isZero
     -- <|> num 

expr :: Parser Expr 
expr = aexp >>= \x -> 
-- acho que percebi bem :), o many1 vai passar pelo sequenciador
-- uma lista de expressões que vão ser associadas à esquerda uma a uma
-- pelo fold ao x e sendo assim "Acumuladas" 
-- para no final retornar a AST
             (many1 aexp >>= \xs -> return (foldl Syntax.App x xs))
             <|> return x


-- Parsing Types 

ty :: Parser Type 
ty = tylit <|> parens type'

tylit :: Parser Type 
tylit =     (reservedOp "1" >> return Unit)
        <|> (reservedOp "Bool" >> return Bool)
        -- <|> (reservedOp "Nat"  >> return Nat )

-- prof só tenho a dizer ...---...
-- EDIT: agora já percebi um bocadinho mais +-
type' :: Parser Type 
type' = Ex.buildExpressionParser tyops ty
    where 
        infixOp x f = Ex.Infix (reservedOp x >> return f)
        tyops = [[
            infixOp "-o" Fun Ex.AssocRight,
            infixOp "(*)" Tensor Ex.AssocLeft,
            infixOp "&" With Ex.AssocLeft,
            infixOp "(+)" Plus Ex.AssocLeft
            -- Prefix op ! ??
            ]]


-- Toplevel

parseExpr :: String -> Either ParseError Expr
parseExpr = parse (contents expr) "<stdin>"

-- parsePE bool "True"
parsePE :: Parser Expr -> String -> Either ParseError Expr
parsePE p = parse p []

-- parsePE :: String -> Either ParseError Expr
-- parsePE = runParser parseExpr [] "untyped lambda-calculus"

-- parseP :: String -> Expr
-- parseP s = fromRight (error "Parsing error") $ runParser parseExpr [] "untyped lambda-calculus" s

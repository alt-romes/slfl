module Parser where

import Prelude hiding (True,False,Bool)

import Lexer
import CoreSyntax
import Syntax

import Text.Parsec
import Text.Parsec.String 
import qualified Text.Parsec.Expr as Ex 


-- Parsing Expressions

variable :: Parser Expr 
variable = Var <$> identifier

-- A -o B
lambda :: Parser Expr 
lambda = do 
    reservedOp "\\"
    x <- identifier
    reservedOp ":"
    t <- type' 
    reservedOp "."
    Syntax.Abs x t <$> expr

-- A (*) B
tensor :: Parser Expr
tensor = do
    e1 <- expr
    reservedOp "(*)"
    Syntax.TensorValue e1 <$> expr

lettensor :: Parser Expr
lettensor = do
    reserved "let"
    n1 <- identifier
    reservedOp "(*)"
    n2 <- identifier
    reservedOp "="
    e1 <- expr
    reserved "in"
    Syntax.LetTensor n1 n2 e1 <$> expr

-- 1
unit :: Parser Expr 
unit = reserved "<>" >> return Syntax.UnitValue

letunit :: Parser Expr
letunit = do
    reserved "let"
    reserved "<>"
    reservedOp "="
    e1 <- expr
    reserved "in"
    Syntax.LetUnit e1 <$> expr

-- A & B
with :: Parser Expr 
with = do 
    e1 <- expr 
    reservedOp "&"
    Syntax.WithValue e1 <$> expr

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
    do -- i.e:  inl True / Bool, inr <> / Bool
    reserved "inl"
    e1 <- expr
    reservedOp "/" -- after the / comes the other type
    t1 <- type'
    return $ Syntax.InjL t1 e1
    <|> 
    do -- i.e:  inl Bool / True, inr Bool / <>
    reserved "inr"
    t1 <- type'
    reservedOp "/" -- before the / comes the other type
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
    reserved "!"
    Syntax.BangValue <$> expr

letbang :: Parser Expr
letbang = do
    reserved "let"
    reserved "!"
    i1 <- identifier
    reservedOp "="
    e1 <- expr
    reserved "in"
    Syntax.LetBang i1 e1 <$> expr

-- Bool
bool :: Parser Expr 
bool =  (reserved "True" >> return Syntax.Tru)
    <|> (reserved "False" >> return Syntax.Fls)
    -- <|> isZero 



-- Parsing sugar expressions

-- if M then N else P
ite :: Parser Expr 
ite = do
    reserved "if"
    cond <- expr 
    reserved "then"
    tr <- expr 
    reserved "else"
    IfThenElse cond tr <$> expr

-- let x = M in N
letin :: Parser Expr
letin = do
    reserved "let"
    i1 <- identifier
    reserved "="
    e1 <- expr
    reserved "in"
    LetIn i1 e1 <$> expr


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
aexp = parens expr 
     <|> variable

     <|> lambda 

     <|> tensor
     <|> lettensor

     <|> unit
     <|> letunit

     <|> with
     <|> proj

     <|> plus
     <|> caseplus

     <|> bang
     <|> letbang

     <|> bool 

     <|> ite 
     <|> letin

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

-- parsePE :: String -> Either ParseError Expr
-- parsePE = runParser parseExpr [] "untyped lambda-calculus"

-- parseP :: String -> Expr
-- parseP s = fromRight (error "Parsing error") $ runParser parseExpr [] "untyped lambda-calculus" s

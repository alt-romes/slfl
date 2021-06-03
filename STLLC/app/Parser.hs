module Parser where

import Prelude hiding (Bool, sum)

import Lexer
import CoreSyntax
import Syntax
import Program

import Text.Parsec
import qualified Text.Parsec.Expr as Ex 

import Data.Maybe
import Data.Either
import Debug.Trace

-- Parsing Expressions

variable :: Parser Expr 
variable = Var <$> identifier

-- A -o B
lambda :: Parser Expr 
lambda = do 
    reservedOp "\\" <|> reservedOp "λ"
    x <- identifier
    t <- option Nothing (do { reservedOp ":"; Just <$> ty })
    try (do { reservedOp "-o"; Syntax.Abs x t <$> expr }) <|> do {reservedOp "->"; Syntax.UnrestrictedAbs x t <$> expr }

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
    do
    reserved "inl"
    e1 <- expr
    t1 <- option Nothing (do { reservedOp ":"; Just <$> ty })
    return $ Syntax.InjL t1 e1
    <|> 
    do
    reserved "inr"
    t1 <- option Nothing (try $ do { t <- ty; reservedOp ":"; return $ Just t})
    Syntax.InjR t1 <$> expr

caseplus :: Parser Expr
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
bool = (reserved "true" >> return Syntax.Tru)
   <|> (reserved "false" >> return Syntax.Fls)
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


-- let x = M in N
letinpattern :: Parser Pattern
letinpattern = VanillaPattern <$> identifier


sumtypebranch :: Parser (String, Maybe Type)
sumtypebranch = do
    tag <- identifier
    t <- option Nothing (do { reservedOp ":"; Just <$> ty })
    reservedOp ";"
    return (tag, t)

sum :: Parser Expr
sum = do
    reserved "union"
    reservedOp "{"
    cls1 <- many (try sumtypebranch)
    tag <- identifier
    e <- expr
    reservedOp ";"
    cls2 <- many (try sumtypebranch)
    reservedOp "}"
    return $ Syntax.SumValue (cls1 ++ cls2) (tag, e)

casebranch :: Parser (String, String, Expr)
casebranch = do
    tag <- identifier
    id <- identifier
    reservedOp "=>"
    e <- expr
    return (tag, id, e)

casesum :: Parser Expr
casesum = do 
    reserved "case"
    e1 <- expr
    reserved "of"
    c1 <- casebranch
    cls <- many (do {reservedOp "|"; casebranch})
    return $ Syntax.CaseOfSum e1 (c1:cls)


caseof :: Parser Expr
caseof = try caseplus
      <|> casesum


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

pairepxr :: Parser Expr
pairepxr = try tensor -- try tensor because "with" is also between "< >"... looks unclear - seria melhor outra opção :)
        <|> try with

aexp :: Parser Expr 
aexp =   parens expr 

     <|> lambda 

     <|> pairepxr

     <|> unit -- not correctly parsing <<>*<>>

     <|> proj

     <|> plus
     <|> sum
     <|> caseof

     <|> bang

     <|> letexp

     <|> bool 

     <|> ite 

     <|> variable

     <|> mark

     -- <|> isZero
     -- <|> num 

expr :: Parser Expr 
expr = aexp >>= \x -> 
         (many1 aexp >>= \xs -> return (foldl Syntax.App x xs))
         <|> return x

-- Typed placeholder for partial synthesis

mark :: Parser Expr
mark = reservedOp "{{" >> (typedmark <|> emptymark)
    where
        typedmark = do
            plhty <- ty
            reservedOp "}}"
            i <- getState
            putState $ i+1
            return $ Syntax.Mark i [] (Just plhty)

        emptymark = do
            reservedOp "..."
            reservedOp "}}"
            i <- getState
            putState $ i+1
            return $ Syntax.Mark i [] Nothing


-- Parsing Types 

ty :: Parser Type 
ty = tylit <|> parens type'

tylit :: Parser Type 
tylit =     sumty
        <|> (reservedOp "1" >> return Unit)
        <|> (reservedOp "Bool" >> return Bool)
        <|> (reservedOp "A" >> return (Atom "A")) -- TODO: Melhor forma de fazer parse de atomos :)
        <|> (reservedOp "B" >> return (Atom "B"))
        <|> (reservedOp "C" >> return (Atom "C"))
        <|> (reservedOp "D" >> return (Atom "D"))
        <|> (reservedOp "E" >> return (Atom "E"))
        <|> (reservedOp "F" >> return (Atom "F"))
        <|> (reservedOp "a" >> return (TypeVar 0)) -- TODO: fazer parse de type variables ?? :)
        <|> (reservedOp "b" >> return (TypeVar 1))
        <|> (reservedOp "c" >> return (TypeVar 2))
        <|> (reservedOp "d" >> return (TypeVar 3))
        <|> (reservedOp "e" >> return (TypeVar 4))
        <|> (reservedOp "f" >> return (TypeVar 5))
        -- <|> (reservedOp "Nat"  >> return Nat )

sumty :: Parser Type
sumty = do
    reservedOp "+"
    reservedOp "{"
    sts <- many1 (do
                    tag <- identifier
                    reservedOp ":"
                    t <- ty
                    reservedOp ";"
                    return (tag, t)
                 )
    reservedOp "}"
    return $ Sum sts


-- ...---...
type' :: Parser Type 
type' = Ex.buildExpressionParser tyops ty
    where 
        infixOp x f = Ex.Infix (reservedOp x >> return f)
        prefixOp x f = Ex.Prefix (reservedOp x >> return f)
        tyops = [[
            infixOp "-o" Fun Ex.AssocRight,
            infixOp "*" Tensor Ex.AssocLeft,
            infixOp "&" With Ex.AssocLeft,
            infixOp "+" Plus Ex.AssocLeft,
            prefixOp "!" Bang
            ]]


-- Parsing modules

argument :: Parser (String, Maybe Type)
argument = do
    argname <- identifier
    argtype <- option Nothing (do { reservedOp ":"; Just <$> ty})
    return (argname, argtype)

letdecl :: Parser Binding
letdecl = do
  reserved "let" <|> reserved "var"
  name <- identifier
  args <- many argument
  reservedOp "="
  body <- expr
  return $ Binding name $ foldr (uncurry Syntax.Abs) body args

datacon :: Parser (Name, Type)
datacon = do
    name <- identifier
    t <- option Unit ty
    return (name, t)

datatype :: Parser ADT
datatype = do
    reserved "data"
    name <- identifier
    reservedOp "="
    con <- datacon
    cons <- many (do {reservedOp "|"; datacon})
    optional (reservedOp ";")
    return $ ADT name (con:cons)

val :: Parser Binding
val = Binding "main" <$> expr

top :: Parser Binding
top = do
  x <- letdecl <|> val
  optional (reservedOp ";") -- TODO : se não meter a ";" não funciona!!!, é tudo menos optional :P
  return x

modl :: Parser Program
modl = do
    adts <- many datatype
    bs <- many top
    return $ Program adts bs


---- TOP LEVEL ------------

parseExpr :: String -> Expr
parseExpr i = case runParser (contents expr) 0 "<stdin>" i of
                Left x -> errorWithoutStackTrace $ "[Expr Parse] Failed: " ++ show x
                Right x -> x

parseModule :: FilePath -> String -> Program
parseModule f i = case runParser (contents modl) 0 f i of
                    Left x -> errorWithoutStackTrace $ "[Module Parse] Failed: " ++ show x
                    Right x -> x

parseType :: String -> Type
parseType i = case runParser (contents ty) 0 "<stdin>" i of
                Left x -> errorWithoutStackTrace $ "[Type Parse] Failed: " ++ show x
                Right x -> x

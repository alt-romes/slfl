module Parser2 where

import Lexer



import Text.Parsec

import Text.Parsec.String 


import qualified Text.Parsec.Expr as Ex 


-- The unsugared ASTs 

type Name = String 

data Type 
    = Fun Type Type
    | Pair Type Type
    | Nat 
    | Bool 
    | Unit 
    deriving (Show)

data Expr 
    = Var Name 
    | Abs Name Type Expr 
    | App Expr Expr 

    | If Expr Expr Expr 
    | Tr
    | Fl 
    | IsZero Expr 

    | Zero 
    | S Expr 

    | PairExp Expr Expr 
    | Proj Int Expr

    | UnitExpr 

    deriving (Show)
   



-- Parsing Expressions

unit :: Parser Expr 
unit = (reserved "()" >> return UnitExpr)

pair :: Parser Expr 
pair = do 
    reserved "("
    e1 <- expr 
    reservedOp ","
    e2 <- expr 
    reserved ")"
    return $ PairExp e1 e2 

proj :: Parser Expr 
proj = 
    do 
    reserved "fst"
    e <- expr 
    return $ Proj 1 e 
    <|>
    do 
    reserved "snd"
    e <- expr 
    return $ Proj 2 e
   


variable :: Parser Expr 
variable = do 
    x <- identifier 
    return (Var x)

num :: Parser Expr 
num =
    (reserved "Z" >> return Zero)
    <|>  
    do 
        reserved "succ"
        n <- expr 
        return $ S n

isZero :: Parser Expr 
isZero = do
    reserved "isZero"
    e <- expr 
    return $ IsZero e 

bool :: Parser Expr 
bool =  (reserved "True" >> return Tr)
    <|> (reserved "False" >> return Fl)
    <|> isZero 

lambda :: Parser Expr 
lambda = do 
    reservedOp "\\"
    x <- identifier
    reservedOp ":"
    t <- type' 
    reservedOp "."
    e <- expr
    return $ Abs x t e 



ite :: Parser Expr 
ite = do
    reserved "if"
    cond <- expr 
    reservedOp "then"
    tr <- expr 
    reserved "else"
    fl <- expr 
    return $ If cond tr fl 



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
             (many1 aexp >>= \xs -> return (foldl App x xs))
             <|> return x



-- Parsing Types 

ty :: Parser Type 
ty = tylit <|> (parens type')

tylit :: Parser Type 
tylit = (reservedOp "Bool" >> return Bool) <|> (reservedOp "Nat" >> return Nat)
        <|> (reservedOp "Unit" >> return Unit)

type' :: Parser Type 
type' = Ex.buildExpressionParser tyops ty
    where 
        infixOp x f = Ex.Infix (reservedOp x >> return f)
        tyops = [ 
            [infixOp "->" Fun Ex.AssocRight, infixOp "," Pair Ex.AssocLeft]
            ]


-- Toplevel

parseExpr :: String -> Either ParseError Expr 
parseExpr input = parse (contents expr) "<stdin>" input

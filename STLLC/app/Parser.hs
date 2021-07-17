module Parser (parseExpr, parseModule, parseType, tylit) where

import Prelude hiding (sum)
import Text.Parsec
import qualified Text.Parsec.Expr as Ex 
import Data.Maybe
import Data.Either
import Debug.Trace


import Lexer
import CoreSyntax hiding (Var(..))
import Syntax
import Program
import Util hiding (parens)



-------------------------------------------------------------------------------
-- Expression Parsing
-------------------------------------------------------------------------------

variable :: Parser Expr 
variable = Var <$> identifier


-- A -o B
lambda :: Parser Expr 
lambda = do 
    reservedOp "\\" <|> reservedOp "λ"
    x <- identifier
    t <- option Nothing (do { reservedOp ":"; Just <$> ty })
    try (do { reservedOp "->"; Syntax.Abs x t <$> expr }) <|> do {reservedOp "=>"; Syntax.UnrestrictedAbs x t <$> expr }


-- A (*) B
tensor :: Parser Expr
tensor = do
    reservedOp "("
    e1 <- expr
    reservedOp ","
    e2 <- expr
    reservedOp ")"
    return $ Syntax.TensorValue e1 e2 


lettensorpattern :: Parser Pattern
lettensorpattern = do
    i1 <- identifier
    reservedOp "*"
    TensorPattern i1 <$> identifier


-- 1
unit :: Parser Expr 
unit = reserved "()" >> return Syntax.UnitValue -- TODO : <<><*><>> breaks...


letunitpattern :: Parser Pattern
letunitpattern = do
    reserved "_"
    return UnitPattern


-- A & B
with :: Parser Expr 
with = do 
    reservedOp "("
    e1 <- expr 
    reservedOp "|"
    e2 <- expr
    reservedOp ")"
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
    t1 <- option Nothing (try $ do { t <- ty; reservedOp ":"; return $ Just t })
    Syntax.InjR t1 <$> expr


caseplus :: Parser Expr
caseplus = do
    reserved "case"
    e1 <- expr
    reserved "of"
    reserved "inl"
    i1 <- identifier
    reservedOp "->"
    e2 <- expr
    reservedOp "|"
    reserved "inr"
    i2 <- identifier
    reservedOp "->"
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
    id <- option "" identifier -- TODO: shouldn't be possible for sum types, but sum types should be generalized to adts?
    reservedOp "->"
    e <- expr
    return (tag, id, e)


casesum :: Parser Expr
casesum = do 
    reserved "case"
    reserved "sum"
    e1 <- expr
    reserved "of"
    c1 <- casebranch
    cls <- many (do {reservedOp "|"; casebranch})
    return $ Syntax.CaseOfSum e1 (c1:cls)


caseadt :: Parser Expr
caseadt = do
    reserved "case"
    e1 <- expr
    reserved "of"
    c1 <- casebranch
    cls <- many (do {reservedOp "|"; casebranch})
    return $ Syntax.CaseOf e1 (c1:cls)


caseof :: Parser Expr
caseof = try casesum
      <|> try caseplus
      <|> caseadt


pairepxr :: Parser Expr
pairepxr = try tensor -- try tensor because "with" is also between "< >"... looks unclear - seria melhor outra opção :)
        <|> try with


num :: Parser Expr
num = Syntax.Lit . LitInt <$> natural


aexp :: Parser Expr 
aexp =   
         pairepxr
     <|> try unit -- not correctly parsing <<>*<>>
     <|> parens expr 
     <|> lambda 
     <|> sum
     <|> proj
     <|> plus
     <|> caseof
     <|> bang
     <|> letexp
     <|> variable
     <|> mark
     <|> num


expr :: Parser Expr 
expr = aexp >>= \x -> 
         (many1 aexp >>= \xs -> return (foldl Syntax.App x xs))
         <|> return x


mark :: Parser Expr
mark = reservedOp "{{" >> (typedmark <|> emptymark)
    where
        typedmark = do
            plhty <- ty
            reservedOp "}}"
            i <- getState
            putState $ i+1
            return $ Syntax.Mark i Nothing ([], []) (Just $ trivialScheme plhty) (0, [])

        emptymark = do
            reservedOp "..."
            reservedOp "}}"
            i <- getState
            putState $ i+1
            return $ Syntax.Mark i Nothing ([], []) Nothing (0, [])





-------------------------------------------------------------------------------
-- Type Parsing
-------------------------------------------------------------------------------

ty :: Parser Type 
ty = tylit <|> parens type'


tylit :: Parser Type 
tylit =     sumty
        <|> try refinementty
        <|> (reservedOp "1" >> return Unit)
        <|> (reserved "Int" >> return (TyLit TyInt))
        <|> (reservedOp "a" >> return (TypeVar 0)) -- !TODO: fazer parse de lowercase identifiers as type variables :)
        <|> (reservedOp "b" >> return (TypeVar 1))
        <|> (reservedOp "c" >> return (TypeVar 2))
        <|> (reservedOp "d" >> return (TypeVar 3))
        <|> (reservedOp "e" >> return (TypeVar 4))
        <|> (reservedOp "f" >> return (TypeVar 5))
        <|> adty -- TODO: can't write ADTs starting by any of those letters above ^:) e não consegui resolver com o try (fazer "starts with uppercase" e assim)


refinementty :: Parser Type
refinementty = do
    name <- identifier
    reservedOp "{"
    typ <- ty
    pred <- option Nothing (do
        reservedOp "|"
        Just <$> predicate
        )
    reservedOp "}"
    return $ RefinementType name typ [] pred

predicate :: Parser Predicate
predicate = Ex.buildExpressionParser tyops predname
    where 
        infixOp x f = Ex.Infix (reservedOp x >> return f)
        prefixOp x f = Ex.Prefix (reservedOp x >> return f)
        tyops = [
            [
            prefixOp "-" (UnaryOp "-")
            ],
            [
            infixOp "+" (BinaryOp "+") Ex.AssocLeft,
            infixOp "-" (BinaryOp "-") Ex.AssocLeft
            ],
            [
            infixOp "*" (BinaryOp "*") Ex.AssocLeft
            ],
            [
            infixOp "!=" (BinaryOp "!=") Ex.AssocNone,
            infixOp "==" (BinaryOp "==") Ex.AssocNone,
            infixOp ">=" (BinaryOp ">=") Ex.AssocNone,
            infixOp ">" (BinaryOp ">") Ex.AssocNone,
            infixOp "<" (BinaryOp "<") Ex.AssocNone,
            infixOp "<=" (BinaryOp "<=") Ex.AssocNone
            ],
            [
            infixOp "&&" (BinaryOp "&&") Ex.AssocLeft,
            infixOp "||" (BinaryOp "||") Ex.AssocLeft,
            infixOp "=>" (BinaryOp "=>") Ex.AssocRight
            ]]

        predname =  (PBool <$> ((reserved "true" >> return True)
                <|> (reserved "false" >> return False)))
                <|> (PVar <$> identifier) <|> (PNum <$> natural) 




sumty :: Parser Type
sumty = do
    reservedOp "sum"
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


adty :: Parser Type
adty = do
    name <- identifier -- TODO: identifier must be uppercase
    ADT name <$> many ty


-- ...---...
type' :: Parser Type 
type' = Ex.buildExpressionParser tyops ty
    where 
        infixOp x f = Ex.Infix (reservedOp x >> return f)
        prefixOp x f = Ex.Prefix (reservedOp x >> return f)
        tyops = [[
            infixOp "->" (Fun . Bang) Ex.AssocRight,
            infixOp "-o" Fun Ex.AssocRight,
            infixOp "*" Tensor Ex.AssocLeft,
            infixOp "&" With Ex.AssocLeft,
            infixOp "+" Plus Ex.AssocLeft,
            prefixOp "!" Bang
            ]]





-------------------------------------------------------------------------------
-- Top (Level) Parsing
-------------------------------------------------------------------------------

argument :: Parser (String, Maybe Type)
argument = do
    argname <- identifier
    argtype <- option Nothing (do { reservedOp ":"; Just <$> ty})
    return (argname, argtype)


letdecl :: Parser (Either TypeBinding Binding)
letdecl = do
    name <- identifier
    args <- many argument
    reservedOp "="
    body <- expr
    return $ Right $ Binding name $ foldr (uncurry Syntax.Abs) body args


typeannot :: Parser (Either TypeBinding Binding)
typeannot = do
    name <- identifier
    reserved "::"
    tyvarnames <- option [] (do
        reserved "forall"
        tvn <- many1 (choice [reservedOp "a" >> return 0, reservedOp "b" >> return 1, reservedOp "c" >> return 2, reservedOp "d" >> return 3, reservedOp "e" >> return 4, reservedOp "f" >> return 5]) -- TODO: anything would be better :p
        dot
        return tvn)
    Left . TypeBinding name . Forall tyvarnames <$> ty


letsynth :: Parser (Either TypeBinding Binding)
letsynth = do
    reserved "synth"
    (Left (TypeBinding name (Forall _ t))) <- typeannot -- TODO: right now marks ignore the schemes, but we could make them such that marks have schemes and the synth function instantiates them
    usenames <- option [] (do
        reservedOp "|"
        reserved "using"
        parens $ many1 identifier
        )
    depth <- option 1 (do
        reservedOp "|"
        reserved "depth"
        natural
        )
    i <- getState
    putState $ i+1
    return $ Right $ Binding name $ Syntax.Mark i Nothing ([], []) (Just $ trivialScheme t) (fromIntegral depth, usenames)


synthrec :: Parser (Either TypeBinding Binding)
synthrec = do
    reserved "synth"
    reserved "rec"
    (Left (TypeBinding name (Forall _ t))) <- typeannot -- TODO: right now marks ignore the schemes, but we could make them such that marks have schemes and the synth function instantiates them
    usenames <- option [] (do
        reservedOp "|"
        reserved "using"
        parens $ many1 identifier
        )
    depth <- option 1 (do
        reservedOp "|"
        reserved "depth"
        natural
        )
    i <- getState
    putState $ i+1
    return $ Right $ Binding name $ Syntax.Mark i (Just name) ([], []) (Just $ trivialScheme t) (fromIntegral depth, usenames)


datacon :: Parser (Name, Type)
datacon = do
    name <- identifier
    t <- option Unit ty
    return (name, t)


datatype :: Parser ADTD
datatype = do
    reserved "data"
    name <- identifier
    typeparams <- many identifier
    reservedOp "="
    con <- datacon
    cons <- many (do {reservedOp "|"; datacon})
    optional (reservedOp ";") -- !TODO: Necessário porque se não as linhas a seguir podem falhar.
    return $ ADTD name (map getNumCode typeparams) (con:cons)


val :: Parser (Either TypeBinding Binding)
val = Right . Binding "main" <$> expr


top :: Parser (Either TypeBinding Binding)
top = do
    x <- try synthrec <|> try letsynth <|> try typeannot <|> try letdecl <|> try val
    optional (reservedOp ";") -- !TODO: Necessário para saber onde uma função termina. Sem o ponto e vírgula não há distinção sobre o que é um identificador de função e o que é uma top level declaration..
    return x

modl :: Parser Program
modl = do
    adts <- many datatype
    bs <- many top
    return $ Program adts (rights bs) (lefts bs) []





-------------------------------------------------------------------------------
-- Exported Functions
-------------------------------------------------------------------------------

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


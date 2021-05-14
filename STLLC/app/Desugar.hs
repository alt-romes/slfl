module Desugar where

import CoreSyntax
import Syntax
import LinearCheck 

import Control.Monad.Reader
import Data.List
import Data.Maybe

data Mult = Linear | Unr | Unknown deriving (Eq)
newtype Var a = Var Mult deriving (Eq)

linVar = Desugar.Var Linear
unVar = Desugar.Var Unr
unknownVar = Desugar.Var Unknown

type DesugarEnv = [(Name, Desugar.Var Index)]
type Desugar = Reader DesugarEnv

inEnv :: (Name, Desugar.Var Index) -> Desugar a -> Desugar a
inEnv (x,e) = local (\env -> (x,e):env)

lookupVar :: Name -> Desugar CoreExpr
lookupVar x = do
    env <- ask
    case lookup x env of
        Just (Desugar.Var mult) -> 
            case mult of
                Linear -> return $ BLVar $ fromJust $ elemIndex (x, Desugar.Var mult) env
                Unr -> return $ BUVar $ fromJust $ elemIndex (x, Desugar.Var mult) env
        Nothing -> return $ FLVar x

desugar :: Expr -> Desugar CoreExpr
desugar (Syntax.Var x) = lookupVar x
    
desugar (Syntax.Abs x t e) = do
    e' <- inEnv (x, linVar) (desugar e)
    return $ CoreSyntax.Abs t e'
desugar (Syntax.App e1 e2) = do
    e1' <- desugar e1
    e2' <- desugar e2
    return $ CoreSyntax.App e1' e2'

desugar (Syntax.TensorValue e1 e2) = do
    e1' <- desugar e1
    e2' <- desugar e2
    return $ CoreSyntax.TensorValue e1' e2'
desugar (Syntax.LetTensor i1 i2 e1 e2) = do
    e1' <- desugar e1
    e2' <- inEnv (i1, linVar) $ inEnv (i2, linVar) $ desugar e2
    return $ CoreSyntax.LetTensor e1' e2'

desugar Syntax.UnitValue = return CoreSyntax.UnitValue
desugar (Syntax.LetUnit e1 e2) = do
    e1' <- desugar e1
    e2' <- desugar e2
    return $ CoreSyntax.LetUnit e1' e2'

desugar (Syntax.WithValue e1 e2) = do
    e1' <- desugar e1
    e2' <- desugar e2
    return $ CoreSyntax.WithValue e1' e2'
desugar (Syntax.Fst e) = CoreSyntax.Fst <$> desugar e
desugar (Syntax.Snd e) = CoreSyntax.Snd <$> desugar e

desugar (Syntax.InjL t e) = CoreSyntax.InjL t <$> desugar e
desugar (Syntax.InjR t e) = CoreSyntax.InjR t <$> desugar e
desugar (Syntax.CaseOfPlus ep i1 e1 i2 e2) = do
    ep' <- desugar ep
    e1' <- inEnv (i1, linVar) $ desugar e1
    e2' <- inEnv (i2, linVar) $ desugar e2
    return $ CoreSyntax.CaseOfPlus ep' e1' e2'

desugar (Syntax.BangValue e) = CoreSyntax.BangValue <$> desugar e
desugar (Syntax.LetBang id e1 e2) = do
    e1' <- desugar e1
    e2' <- inEnv (id, unVar) (desugar e2)
    return $ CoreSyntax.LetBang e1' e2'

desugar (Syntax.IfThenElse e1 e2 e3) = do
    e1' <- desugar e1
    e2' <- desugar e2
    CoreSyntax.IfThenElse e1' e2' <$> desugar e3

desugar Syntax.Tru = return CoreSyntax.Tru
desugar Syntax.Fls = return CoreSyntax.Fls

desugar (Syntax.LetIn id e1 e2) = do
    e1' <- desugar e1
    abs <- desugar (Syntax.Abs id (typecheck e1') e2)
    return $ CoreSyntax.App abs e1'


desugarModule :: [Binding] -> [CoreBinding]
desugarModule = map desugarModule'
    where desugarModule' (name, exp) = (name, runReader (desugar exp) []) 


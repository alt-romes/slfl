module Desugar (desugarExpr, desugarModule) where

import Control.Monad.Reader
import Data.List
import Data.Maybe
import Debug.Trace


import CoreSyntax hiding (Var(..), Mult(..))
import Syntax
import Program



-------------------------------------------------------------------------------
-- Datatypes
-------------------------------------------------------------------------------

newtype Var a = Var Mult deriving (Eq, Show)
data Mult = Linear | Unr | Unknown deriving (Eq, Show)

linVar = Desugar.Var Linear
unVar = Desugar.Var Unr
unknownVar = Desugar.Var Unknown

type DesugarEnv = [(Name, Desugar.Var Mult)]
type Desugar = Reader DesugarEnv





-------------------------------------------------------------------------------
-- Functions
-------------------------------------------------------------------------------

lookupVar :: Name -> Desugar CoreExpr
lookupVar x = do
    env <- ask
    case lookup x env of
        Just (Desugar.Var mult) -> 
            case mult of
                Linear -> return $ BLVar $ fromJust $ elemIndex (x, Desugar.Var mult) env
                Unr -> return $ BUVar $ fromJust $ elemIndex (x, Desugar.Var mult) env
        Nothing -> return $ FUVar x


inEnv :: (Name, Desugar.Var Mult) -> Desugar a -> Desugar a
inEnv (x,e) = local (\env -> (x,e):env)





-------------------------------------------------------------------------------
-- Main Logic
-------------------------------------------------------------------------------

desugar :: Expr -> Desugar CoreExpr
desugar (Syntax.Lit x) = return $ CoreSyntax.Lit x

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

desugar (Syntax.LetIn id e1 e2) = do
    e1' <- desugar e1
    e2' <- inEnv (id, unVar) (desugar e2)
    return $ CoreSyntax.LetIn e1' e2' -- se quisesse fazer desugar do let in para uma abstração tinha também de passar todo o contexto para o typechecker, porque sem passar mais informação ela é incompleta

desugar (Syntax.Mark i n c t) = return $ CoreSyntax.Mark i n ([], []) t


desugar (Syntax.SumValue mts (t, e)) = do
    e' <- desugar e
    return $ CoreSyntax.SumValue mts (t, e')
desugar (Syntax.CaseOfSum e exps) = do
    e' <- desugar e
    exps' <- mapM (\(t, i, ex) -> do {ex' <- inEnv (i, linVar) (desugar ex); return (t, ex')}) exps
    return $ CoreSyntax.CaseOfSum e' exps'

desugar (Syntax.CaseOf e exps) = do
    e' <- desugar e
    exps' <- mapM (\(t, i, ex) ->
        if i == ""
           then do
               ex' <- desugar ex
               return (t, ex')
           else do
               ex' <- inEnv (i, linVar) (desugar ex)
               return (t, ex')
       ) exps
    return $ CoreSyntax.CaseOf e' exps'

desugar (Syntax.UnrestrictedAbs i (Just t) e) = desugar (Syntax.Abs i (Just $ Bang t) (Syntax.LetBang i (Syntax.Var i) e))
desugar (Syntax.UnrestrictedAbs i Nothing e) = desugar (Syntax.Abs i Nothing (Syntax.LetBang i (Syntax.Var i) e))





-------------------------------------------------------------------------------
-- "Prelude"
-------------------------------------------------------------------------------

pmult :: TypeBinding
pmult = TypeBinding "multiply" $ trivialScheme (Fun trivialNat (Fun trivialNat trivialNat))

psub :: TypeBinding
psub = TypeBinding "subtract" $ trivialScheme (Fun trivialNat (Fun trivialNat trivialNat))

psum :: TypeBinding
psum = TypeBinding "add" $ trivialScheme (Fun trivialNat (Fun trivialNat trivialNat))

addPrelude :: [TypeBinding] -> [TypeBinding]
addPrelude ts = ts ++ [psum]




-------------------------------------------------------------------------------
-- Exported Functions
-------------------------------------------------------------------------------

desugarExpr :: Expr -> CoreExpr
desugarExpr exp = runReader (desugar exp) []


desugarModule :: Program -> Program
desugarModule (Program adts bindings ts cs) = Program adts bindings (addPrelude ts) $ map desugarModule' bindings
    where desugarModule' (Binding name exp) = CoreBinding name $ runReader (desugar exp) [] 


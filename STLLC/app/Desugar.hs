module Desugar (desugarExpr, desugarModule) where

import Control.Monad.Reader
import Control.Monad.State
import Data.List
import Data.Maybe
import Debug.Trace


import CoreSyntax hiding (Var(..), Mult(..))
import Syntax
import Program
import Util



-------------------------------------------------------------------------------
-- Datatypes
-------------------------------------------------------------------------------

newtype Var a = Var Mult deriving (Eq, Show)
data Mult = Linear | Unr | Unknown deriving (Eq, Show)

linVar = Desugar.Var Linear
unVar = Desugar.Var Unr
unknownVar = Desugar.Var Unknown

type DesugarEnv = [(Name, Desugar.Var Mult)]
type Desugar = StateT Int (Reader DesugarEnv)





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

fresh :: Desugar Name
fresh = do
    i <- get
    put $ i + 1
    return $ getName i




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

desugar (Syntax.Mark i n c t (e,f,g,h)) = do
    h' <- maybe (return Nothing) ((Just <$>) . desugar) h
    return $ CoreSyntax.Mark i n ([], []) t (e,f,g, h')

desugar (Syntax.SumValue mts (t, e)) = do
    e' <- desugar e
    return $ CoreSyntax.SumValue mts (t, e')
desugar (Syntax.CaseOfSum e exps) = do
    e' <- desugar e
    exps' <- mapM (\(t, i, ex) -> do {ex' <- inEnv (i, linVar) (desugar ex); return (t, ex')}) exps
    return $ CoreSyntax.CaseOfSum e' exps'

desugar (Syntax.CaseOf e exps) = do
    e' <- desugar e
    exps' <- mapM (\(t, i, ex) -> do
           ex' <- inEnv (i, linVar) (desugar ex)
           return (t, ex')
       ) exps
    return $ CoreSyntax.CaseOf e' exps'

desugar (Syntax.CaseOfPattern e exps) = do
    exps' <- expsf'
    desugar (Syntax.CaseOf e exps')
        where
        expsf' :: Desugar [(Name, Name, Expr)]
        expsf' = mapM reducePatterns exps 

        reducePatterns :: (Name, Pattern, Expr) -> Desugar (Name, Name, Expr)
        reducePatterns (t, pat, ex) = do
            i <- get
            put $ i + 1
            case pat of
                UnitPattern -> return (t, "", ex)
                VanillaPattern n -> return (t, n, ex)
                BangPattern p1 -> do
                          n1 <- fresh
                          e' <- deconspattern (Syntax.Var n1) ex (BangPattern p1)
                          return (t, n1, e')
                TensorPattern p1 p2 -> do
                          n1 <- fresh
                          e' <- deconspattern (Syntax.Var n1) ex (TensorPattern p1 p2)
                          return (t, n1, e')


desugar (Syntax.LetInPattern pat e1 e2) =
    deconspattern e1 e2 pat >>= desugar

desugar (Syntax.UnrestrictedAbs i (Just t) e) = desugar (Syntax.Abs i (Just $ Bang t) (Syntax.LetBang i (Syntax.Var i) e))
desugar (Syntax.UnrestrictedAbs i Nothing e) = desugar (Syntax.Abs i Nothing (Syntax.LetBang i (Syntax.Var i) e))

desugar (ExpBop a b c) = do
    b' <- desugar b
    c' <- desugar c
    return $ CExpBop a b' c'


deconspattern :: Expr -> Expr -> Pattern -> Desugar Expr
deconspattern e1 e2 UnitPattern = return $ Syntax.LetUnit e1 e2
deconspattern e1 e2 (VanillaPattern n) = return $ Syntax.LetIn n e1 e2 -- In theory the other cases won't send it here - only actual let ins should get here
deconspattern e1 e2 (TensorPattern p1 p2) = do
    case p1 of
      VanillaPattern n1 ->
          case p2 of
            VanillaPattern n2 -> return $ Syntax.LetTensor n1 n2 e1 e2
            _ -> do
                n2 <- fresh
                e2' <- deconspattern (Syntax.Var n2) e2 p2
                return $ Syntax.LetTensor n1 n2 e1 e2'
      _ -> case p2 of
            VanillaPattern n2 -> do
                n1 <- fresh
                e2' <- deconspattern (Syntax.Var n1) e2 p1
                return $ Syntax.LetTensor n1 n2 e1 e2'
            _ -> do
                n1 <- fresh
                n2 <- fresh
                e2' <- deconspattern (Syntax.Var n1) e2 p1
                e2'' <- deconspattern (Syntax.Var n2) e2' p2
                return $ Syntax.LetTensor n1 n2 e1 e2''
deconspattern e1 e2 (BangPattern p1) = do
    case p1 of
      VanillaPattern n1 -> return $ Syntax.LetBang n1 e1 e2
      _ -> do
          n1 <- fresh
          e2' <- deconspattern (Syntax.Var n1) e2 p1
          return $ Syntax.LetBang n1 e1 e2'






-------------------------------------------------------------------------------
-- "Prelude"
-------------------------------------------------------------------------------


addPrelude :: [TypeBinding] -> [TypeBinding]
addPrelude ts = ts -- ++ builtinfs




-------------------------------------------------------------------------------
-- Exported Functions
-------------------------------------------------------------------------------

desugarExpr :: Expr -> CoreExpr
desugarExpr exp = runReader (evalStateT (desugar exp) 0) []


desugarModule :: Program -> Program
desugarModule (Program adts bindings ts cs) = Program adts bindings (addPrelude ts) $ map desugarModule' bindings
    where desugarModule' (Binding name exp) = CoreBinding name $ runReader (evalStateT (desugar exp) 0) [] 


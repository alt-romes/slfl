module Desugar where

import CoreSyntax
import Syntax
import LinearSequentCheck

import Control.Monad.Reader

type Name = String
type Index = Int


-- Acho que seria bom falarmos sobre isto mais um bocado professor,
-- Gostava de rever.

data Mult = Linear | Unr | Unknown
data Var a = Var { multiplicity :: Mult,
                              get :: a }

linVar x = Desugar.Var{multiplicity=Linear, get=x}
unVar x = Desugar.Var{multiplicity=Unr, get=x}
unknownVar x = Desugar.Var{multiplicity=Unknown,get=x}

type DesugarEnv = [(Name, Desugar.Var Index)]
type Desugar = Reader DesugarEnv -- gostava tmb de ver a Monad na doc com ajuda, porque não sei ler aquilo bem

inEnv :: (Name, Desugar.Var Index) -> Desugar a -> Desugar a
inEnv (x,e) = local (\env -> (x,e):env)

lookupVar :: Name -> Desugar CoreExpr
lookupVar x = do
    env <- ask
    case lookup x env of
        Just var -> 
            case multiplicity var of
                Linear -> return $ BLVar $ get var
                Unr -> return $ BUVar $ get var
        Nothing -> return $ FLVar x

desugar :: Expr -> Desugar CoreExpr
desugar = desugar' 0
    where
        desugar' _ (Syntax.Var x) = lookupVar x
            
        desugar' n (Syntax.Abs x t e) = do
            e' <- inEnv (x, linVar n) (desugar' (n+1) e)
            return $ CoreSyntax.Abs t e'
        desugar' n (Syntax.App e1 e2) = do
            e1' <- desugar' n e1
            e2' <- desugar' n e2
            return $ CoreSyntax.App e1' e2'

        desugar' n (Syntax.TensorValue e1 e2) = do
            e1' <- desugar' n e1
            e2' <- desugar' n e2
            return $ CoreSyntax.TensorValue e1' e2'
        desugar' n (Syntax.LetTensor i1 i2 e1 e2) = do
            e1' <- desugar' n e1
            e2' <- inEnv (i1, linVar n) $ inEnv (i2, linVar (n+1)) $ desugar' (n+2) e2
            return $ CoreSyntax.LetTensor e1' e2'

        desugar' _ Syntax.UnitValue = return CoreSyntax.UnitValue
        desugar' n (Syntax.LetUnit e1 e2) = do
            e1' <- desugar' n e1
            e2' <- desugar' n e2
            return $ CoreSyntax.LetUnit e1' e2'

        desugar' n (Syntax.WithValue e1 e2) = do
            e1' <- desugar' n e1
            e2' <- desugar' n e2
            return $ CoreSyntax.WithValue e1' e2'
        desugar' n (Syntax.Fst e) = CoreSyntax.Fst <$> desugar' n e
        desugar' n (Syntax.Snd e) = CoreSyntax.Snd <$> desugar' n e
        
        desugar' n (Syntax.InjL t e) = CoreSyntax.InjL t <$> desugar' n e
        desugar' n (Syntax.InjR t e) = CoreSyntax.InjR t <$> desugar' n e
        desugar' n (Syntax.CaseOfPlus ep i1 e1 i2 e2) = do
            ep' <- desugar' n ep
            e1' <- inEnv (i1, linVar n) $ desugar' (n+1) e1
            e2' <- inEnv (i2, linVar n) $ desugar' (n+1) e2
            return $ CoreSyntax.CaseOfPlus ep' e1' e2'

        desugar' n (Syntax.BangValue e) = CoreSyntax.BangValue <$> desugar' n e
        desugar' n (Syntax.LetBang id e1 e2) = do
            e1' <- desugar' n e1
            e2' <- inEnv (id, unVar n) (desugar' (n+1) e2)
            return $ CoreSyntax.LetBang e1' e2'

        desugar' n (Syntax.IfThenElse e1 e2 e3) = do
            e1' <- desugar' n e1
            e2' <- desugar' n e2
            CoreSyntax.IfThenElse e1' e2' <$> desugar' n e3

        desugar' _ Syntax.Tru = return CoreSyntax.Tru
        desugar' _ Syntax.Fls = return CoreSyntax.Fls

        desugar' n (Syntax.LetIn id e1 e2) = do
            e1' <- desugar' n e1
            abs <- desugar' n (Syntax.Abs id (typecheck e1') e2)
            return $ CoreSyntax.App abs e1'


-- type Ctxt = [(String, Int)]

-- desugar :: Desugar.Ctxt -> Expr -> CoreExpr

-- desugar ctxt (Var id) = maybe (FLVar id) BLVar (lookup id ctxt)

-- desugar ctxt (Syntax.Abs id t e) = CoreSyntax.Abs t (desugar ((id, length ctxt):ctxt) e)
-- desugar ctxt (Syntax.App e1 e2) = CoreSyntax.App (desugar ctxt e1) (desugar ctxt e2)

-- desugar ctxt (Syntax.TensorValue e1 e2) = CoreSyntax.TensorValue (desugar ctxt e1) (desugar ctxt e2)
-- desugar ctxt (Syntax.LetTensor i1 i2 e1 e2) = CoreSyntax.LetTensor i1 i2 (desugar ctxt e1) (desugar ctxt e2)

-- desugar ctxt Syntax.UnitValue = CoreSyntax.UnitValue
-- desugar ctxt (Syntax.LetUnit e1 e2) = CoreSyntax.LetUnit (desugar ctxt e1) (desugar ctxt e2)

-- desugar ctxt (Syntax.WithValue e1 e2) = CoreSyntax.WithValue (desugar ctxt e1) (desugar ctxt e2)
-- desugar ctxt (Syntax.Fst e) = CoreSyntax.Fst $ desugar ctxt e
-- desugar ctxt (Syntax.Snd e) = CoreSyntax.Snd $ desugar ctxt e

-- desugar ctxt (Syntax.InjL t e) = CoreSyntax.InjL t $ desugar ctxt e
-- desugar ctxt (Syntax.InjR t e) = CoreSyntax.InjR t $ desugar ctxt e
-- desugar ctxt (Syntax.CaseOfPlus ep i1 e1 i2 e2) = CoreSyntax.CaseOfPlus (desugar ctxt ep) i1 (desugar ctxt e1) i2 (desugar ctxt e2)

-- desugar ctxt (Syntax.BangValue e) = CoreSyntax.BangValue $ desugar ctxt e
-- desugar ctxt (Syntax.LetBang id e1 e2) = CoreSyntax.LetBang id (desugar ctxt e1) (desugar ctxt e2)

-- desugar ctxt (Syntax.IfThenElse e1 e2 e3) = CoreSyntax.IfThenElse (desugar ctxt e1) (desugar ctxt e2) (desugar ctxt e3)

-- desugar ctxt Syntax.Tru = CoreSyntax.Tru
-- desugar ctxt Syntax.Fls = CoreSyntax.Fls

-- desugar ctxt (LetIn id e1 e2) =
--     let des1 = desugar ctxt e1 in
--         CoreSyntax.App (desugar ctxt $ Syntax.Abs id (typecheck des1) e2) des1

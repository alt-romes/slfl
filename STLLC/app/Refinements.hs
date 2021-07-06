module Refinements (satunifyrefinements) where 

import Control.Monad.State
import Debug.Trace
import Data.Set hiding (map)
import qualified Data.Map as Map
import Data.Bifunctor
import Data.List (intercalate)

import CoreSyntax
import Util


data VerificationCondition
    = VCTrue (Set (Name, Type))
    | VCPred (Set (Name, Type)) Predicate
    | VCImpl (Set (Name, Type)) [Predicate]
    | VCConj VerificationCondition VerificationCondition


instance Show VerificationCondition where
    show (VCTrue s) = "∀" ++ intercalate ", " (map (\(n,t) -> n ++ ":" ++ show t) (toList s)) ++ " |- true"
    show (VCPred s p) = "∀" ++ intercalate ", " (map (\(n,t) -> n ++ ":" ++ show t) (toList s)) ++ " |- " ++ show p
    show (VCImpl s ps) = "∀" ++ intercalate ", " (map (\(n,t) -> n ++ ":" ++ show t) (toList s)) ++ " |- " ++ intercalate " => " (map show ps)
    show (VCConj v1 v2) = show v1 ++ " /\\ " ++ show v2



replaceName :: Map.Map Name Name -> Predicate -> Predicate
replaceName m p = case p of
    PVar n' -> case Map.lookup n' m of
                 Nothing -> PVar n'
                 Just n'' -> PVar n''
    PNum x -> PNum x
    BinaryOp opn p1 p2 -> BinaryOp opn (replaceName m p1) (replaceName m p2)
    Conjunction p1 p2 -> Conjunction (replaceName m p1) (replaceName m p2)

addentry :: Name -> Name -> State (Int, Map.Map Name Name) ()
addentry n n' = modify $ second $ Map.insert n n'

fresh :: State (Int, Map.Map Name Name) Name
fresh = do
    (i, m) <- get
    put (i + 1, m)
    return $ getName i

renameR :: Type -> Type
renameR t = evalState (renameR' t) (0, Map.empty)
    where
        renameR' :: Type -> State (Int, Map.Map Name Name) Type
        renameR' t = case t of
            Fun t1 t2 -> do
                t1' <- renameR' t1
                t2' <- renameR' t2
                return $ Fun t1' t2'
            RefinementType n t' (Just p) -> do
                nname <- fresh
                addentry n nname
                m <- gets snd
                return $ RefinementType nname t' (Just $ replaceName m p)
            RefinementType n t' Nothing -> do
                nname <- fresh
                addentry n nname
                return $ RefinementType nname t' Nothing
            t' -> return t' -- TODO: What to do with other types inside a dependent function?


composeVC :: VerificationCondition -> VerificationCondition -> VerificationCondition
composeVC (VCTrue s) (VCTrue s') = VCTrue (s' `union` s) -- I wonder if this whole function makes sense
composeVC (VCTrue s) (VCPred s' p) = VCPred (s' `union` s) p
composeVC (VCTrue s) (VCImpl s' ps) = VCImpl (s' `union` s) ps
composeVC (VCPred s p) (VCTrue s') = VCTrue (s' `union` s)
composeVC (VCPred s p) (VCPred s' p') = VCImpl (s' `union` s) [p, p']
composeVC (VCPred s p) (VCImpl s' ps) = VCImpl (s' `union` s) (p:ps)
composeVC (VCImpl s ps) (VCTrue s') = VCTrue (s' `union` s)
composeVC (VCImpl s ps) (VCPred s' p') = VCImpl (s' `union` s) (ps ++ [p'])
composeVC (VCImpl s ps) (VCImpl s' ps') = VCImpl (s' `union` s) (ps ++ ps')
composeVC x (VCConj v1 v2) = VCConj (x `composeVC` v1) (x `composeVC` v2)
composeVC (VCConj v1 v2) y = y
-- composeVC x y = error ("[Refinement] Composing " ++ show x ++ " with " ++ show y)


getvc :: Type -> VerificationCondition
getvc t = case t of
    Fun t1 t2 -> do
        let vct1 = getvc t1
        let vct2 = vct1 `composeVC` getvc t2
        VCConj vct1 vct2
    RefinementType n t' (Just p) -> VCPred (singleton (n, t')) p
    RefinementType n t' Nothing -> VCTrue (singleton (n, t'))
    t' -> VCTrue empty -- TODO: What to do with other types inside a dependent function?


satunifyrefinements :: Type -> Type -> Bool
satunifyrefinements t t' = do -- Rename to match the refinement variables in the two types so that the composition is useful
    satvc (getvc (renameR t) `composeVC` getvc (renameR t'))



satvc :: VerificationCondition -> Bool
satvc vc = traceShow vc True
    



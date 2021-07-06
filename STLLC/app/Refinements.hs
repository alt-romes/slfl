module Refinements (satunifyrefinements, getvc, renameR, composeVC, replaceName) where 

import Control.Monad.State
import Debug.Trace
import Data.Maybe
import Data.Set as Set hiding (map, foldr)
import qualified Data.Map as Map
import Data.Bifunctor
import Data.List (intercalate)
import Data.SBV as SBV hiding (Predicate)

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
            RefinementType n t' ls (Just p) -> do
                nname <- fresh
                addentry n nname
                ls' <- mapM renameR' ls
                m <- gets snd
                return $ RefinementType nname t' ls' (Just $ replaceName m p)
            RefinementType n t' ls Nothing -> do
                nname <- fresh
                addentry n nname
                ls' <- mapM renameR' ls
                return $ RefinementType nname t' ls' Nothing
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
composeVC (VCConj v1 v2) (VCConj v1' v2') = VCConj (v1 `composeVC` v1') (v2 `composeVC` v2')
composeVC x (VCConj v1 v2) = VCConj (x `composeVC` v1) (x `composeVC` v2)
composeVC vc@(VCConj v1 v2) (VCTrue _) = vc
-- composeVC (VCConj v1 v2) y = y
composeVC x y = error ("[Refinement] Composing " ++ show x ++ " with " ++ show y)


getvc :: Type -> VerificationCondition
getvc t = case t of
    Fun t1 t2 -> do
        let vct1 = getvc t1
        let vct2 = vct1 `composeVC` getvc t2
        VCConj vct1 vct2
    RefinementType n t' ls (Just p) -> foldr (composeVC . getvc) (VCPred (singleton (n, t')) p) ls
    RefinementType n t' ls Nothing -> foldr (composeVC . getvc) (VCTrue (singleton (n, t'))) ls

    t' -> VCTrue empty  -- TODO: What to do with other types inside a dependent function?


satunifyrefinements :: Type -> Type -> IO Bool
satunifyrefinements t t' = do -- Rename to match the refinement variables in the two types so that the composition is useful
    trace ("composing " ++ show (getvc (renameR t)) ++ "\nwith " ++ show (getvc (renameR t')) ++ "\nto get " ++ show (getvc (renameR t) `composeVC` getvc (renameR t'))) $ satvc (getvc (renameR t) `composeVC` getvc (renameR t'))



satvc :: VerificationCondition -> IO Bool
satvc vc = case vc of
    VCTrue _ -> return True
    VCPred s p -> modelExists <$> res
        where
            res :: IO SatResult
            res = sat $ do
                intls <- mapM (\(n,t) -> makeSInt (n,t) >>= \x' -> return (n, x')) (toList $ Set.filter (isInt . snd) s)
                constrainPred intls p

    VCImpl s ps -> modelExists <$> res
        where
            res :: IO SatResult
            res = sat $ do
                intls <- mapM (\(n,t) -> makeSInt (n,t) >>= \x' -> return (n, x')) (toList $ Set.filter (isInt . snd) s)
                mapM_ (constrainPred intls) ps
        

    VCConj v1 v2 -> do
        s1 <- satvc v1
        s2 <- satvc v2
        return $ s1 && s2


makeSInt :: (String, Type) -> Symbolic SInteger
makeSInt (n, TyLit TyInt) = sInteger n


constrainPred :: [(Name, SInteger)] -> Predicate -> Symbolic ()
constrainPred ls (BinaryOp name p1 p2)
    | name == "==" = do
        (sv1, sv2) <- getSVals ls p1 p2
        constrain $ sv1 .== sv2

    | name == ">=" = do
        (sv1, sv2) <- getSVals ls p1 p2
        constrain $ sv1 .>= sv2

    | name == ">" = do
        (sv1, sv2) <- getSVals ls p1 p2
        constrain $ sv1 .> sv2

    | name == "<" = do
        (sv1, sv2) <- getSVals ls p1 p2
        constrain $ sv1 .< sv2

    | name == "<=" = do
        (sv1, sv2) <- getSVals ls p1 p2
        constrain $ sv1 .<= sv2

    | otherwise = error ("[Refinement] No boolean op in predicate " ++ show (BinaryOp name p1 p2))

    where
        getSVals ls p1 p2 = do
            sv1 <- getSValPred ls p1
            sv2 <- getSValPred ls p2
            return (sv1, sv2)


getSValPred :: [(Name, SInteger)] -> Predicate -> Symbolic SInteger
getSValPred ls (BinaryOp name p1 p2)

    | name == "+" = do
        sv1 <- getSValPred ls p1
        sv2 <- getSValPred ls p2
        return $ sv1 + sv2

    | name == "-" = do
        sv1 <- getSValPred ls p1
        sv2 <- getSValPred ls p2
        return $ sv1 - sv2

    | name == "*" = do
        sv1 <- getSValPred ls p1
        sv2 <- getSValPred ls p2
        return $ sv1 * sv2
       
    | otherwise = error "[Refinement] Error 6"

getSValPred ls (PVar n) =
    case lookup n ls of
        Just sv -> return sv
        Nothing -> error ("[Refinement] No symbolic integer variable " ++ show n ++ " in " ++ show ls)

getSValPred ls (PNum i) = return $ literal i

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
    PBool x -> PBool x
    BinaryOp opn p1 p2 -> BinaryOp opn (replaceName m p1) (replaceName m p2)

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
                nname <- newname n
                state <- get
                ls' <- mapM renameR' ls
                m <- gets snd
                put state  -- Reset state after renaming the context variables for this refined type
                           -- the letters used for the context aren't important
                           -- because they come after all dependent variables used in this type
                           -- And this way we keep the dependent variables correctly named which is crucial for the refinements to work
                return $ RefinementType nname t' ls' (Just $ replaceName m p)
            RefinementType n t' ls Nothing -> do
                nname <- newname n
                state <- get
                ls' <- mapM renameR' ls
                put state
                return $ RefinementType nname t' ls' Nothing
            t' -> return t' -- TODO: What to do with other types inside a dependent function?

        newname n = do
            m <- gets snd
            case Map.lookup n m of
              Nothing -> do
                nname <- fresh
                addentry n nname
                return nname
              Just nname -> return nname


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
    satvc (getvc (renameR t) `composeVC` getvc (renameR t'))



satvc :: VerificationCondition -> IO Bool
satvc vc = case vc of
    VCTrue _ -> return True
    VCPred s p -> modelExists <$> res
        where
            res :: IO SatResult
            res = sat $ do
                symls <- mapM (\(n,t) -> makeSVar (n,t) >>= \x' -> return (n, x')) (toList s)
                Left sv <- getSValPred symls p
                constrain sv

    VCImpl s ps -> modelExists <$> res
        where
            res :: IO SatResult
            res = sat $ do
                symls <- mapM (\(n,t) -> makeSVar (n,t) >>= \x' -> return (n, x')) (toList s)
                mapM_ (getSValPred symls >=> \(Left sv) -> constrain sv) ps
        

    VCConj v1 v2 -> do
        s1 <- satvc v1
        s2 <- satvc v2
        return $ s1 && s2


makeSVar :: (Name, Type) -> Symbolic (Either SBool SInteger)
makeSVar (n, ADT _ _) = Left <$> sBool n
makeSVar (n, TyLit TyInt) = Right <$> sInteger n
makeSVar (n, t) = error ("[Refinement] Can't make symbolic variable " ++ show n ++ " of type " ++ show t)


getSVals :: [(Name, Either SBool SInteger)] -> Predicate -> Predicate -> Symbolic (Either SBool SInteger, Either SBool SInteger)
getSVals ls p1 p2 = do
    sv1 <- getSValPred ls p1
    sv2 <- getSValPred ls p2
    return (sv1, sv2)


getSValPred :: [(Name, Either SBool SInteger)] -> Predicate -> Symbolic (Either SBool SInteger)
getSValPred ls (BinaryOp name p1 p2)

    | name == "+" = do
        (Right sv1, Right sv2) <- getSVals ls p1 p2
        return $ Right $ sv1 + sv2

    | name == "-" = do
        (Right sv1, Right sv2) <- getSVals ls p1 p2
        return $ Right $ sv1 - sv2

    | name == "*" = do
        (Right sv1, Right sv2) <- getSVals ls p1 p2
        return $ Right $ sv1 * sv2

    | name == "==" = do
        (Right sv1, Right sv2) <- getSVals ls p1 p2
        return $ Left $ sv1 .== sv2

    | name == "!=" = do
        (sv1, sv2) <- getSVals ls p1 p2
        return $ Left $ sv1 ./= sv2

    | name == ">=" = do
        (sv1, sv2) <- getSVals ls p1 p2
        return $ Left $ sv1 .>= sv2

    | name == ">" = do
        (sv1, sv2) <- getSVals ls p1 p2
        return $ Left $ sv1 .> sv2

    | name == "<" = do
        (sv1, sv2) <- getSVals ls p1 p2
        return $ Left $ sv1 .< sv2

    | name == "<=" = do
        (sv1, sv2) <- getSVals ls p1 p2
        return $ Left $ sv1 .<= sv2

    | name == "&&" = do
        (Left sv1, Left sv2) <- getSVals ls p1 p2
        return $ Left $ sv1 .&& sv2

    | name == "||" = do
        (Left sv1, Left sv2) <- getSVals ls p1 p2
        return $ Left $ sv1 .|| sv2
       
    | otherwise = error "[Refinement] Error 6"

getSValPred ls (PVar n) =
    case lookup n ls of
        Just ebi -> case ebi of
            Left v -> return $ Left v
            Right v -> return $ Right v

        Nothing -> error ("[Refinement] No symbolic integer variable " ++ show n ++ " in " ++ show ls)

getSValPred ls (PNum i) = return $ Right $ literal i

getSValPred ls (PBool x) = if x then return $ Left sTrue else return $ Left sFalse

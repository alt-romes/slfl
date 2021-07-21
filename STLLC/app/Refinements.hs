{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Refinements (satunifyrefinements, getvc, renameR, composeVC,
    replaceName, addRefinementToCtxs, getModelExpr, getRefName, isRefType) where 

import Control.Monad.State
import Lexer
import Data.Either (lefts)
import Parser (tylit)
import Text.Parsec hiding (State)
import Debug.Trace
import Data.Maybe
import Data.Set as Set hiding (map, foldr, foldl, null)
import qualified Data.Map as Map
import Data.Bifunctor
import Data.List (intercalate)
import Data.SBV as SBV hiding (Predicate, forall)
import Data.SBV.Trans.Control (SMTOption(..))
import Data.SBV.Control hiding (fresh, getModel)
import Data.SBV.Internals hiding (State, Abs)

import CoreSyntax hiding (Abs, Var)
import Syntax
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


isRefType :: Type -> Bool
isRefType RefinementType {} = True
isRefType _ = False

getRefName :: Type -> Name
getRefName (RefinementType n _ _ _) = n

getRefType :: Type -> Type
getRefType (RefinementType _ t _ _) = t

addRefinementToCtxs :: Type -> Type -> Type
addRefinementToCtxs r = transformType (\case RefinementType rn rt ls mp -> RefinementType rn rt (r:ls) mp; t' -> t')

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


satunifyrefinements :: Type -> Type -> IO Bool -- Satisfy unifying two refinement types where t subtypes t'
satunifyrefinements t t' = -- Rename to match the refinement variables in the two types so that the composition is useful
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
            res = satWith z3 $ do -- {verbose = True}
                symls <- mapM (\(n,t) -> makeUnivSVar (n,t) >>= \x' -> return (n, x')) (toList s)
                sympreds <- lefts <$> mapM (getSValPred symls) ps
                when (length sympreds /= length ps) (error "All top level symvals should be predicates.")
                constrain $ foldr1 (.=>) sympreds
        
    VCConj v1 v2 -> do
        s1 <- satvc v1
        s2 <- satvc v2
        return $ s1 && s2


makeSVar :: (Name, Type) -> Symbolic (Either SBool SInteger)
makeSVar (n, ADT _ _) = Left <$> sBool n
makeSVar (n, TyLit TyInt) = Right <$> sInteger n
makeSVar (n, t) = error ("[Refinement] Can't make symbolic variable " ++ show n ++ " of type " ++ show t)

makeUnivSVar :: (Name, Type) -> Symbolic (Either SBool SInteger)
makeUnivSVar (n, ADT _ _) = Left <$> forall n
makeUnivSVar (n, TyLit TyInt) = Right <$> forall n
makeUnivSVar (n, t) = error ("[Refinement] Can't make universal symbolic variable " ++ show n ++ " of type " ++ show t)

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

    | name == "=>" = do
        (Left sv1, Left sv2) <- getSVals ls p1 p2
        return $ Left $ sv1 .=> sv2
       
    | otherwise = error "[Refinement] Error 6"

getSValPred ls (PVar n) =
    case lookup n ls of
        Just ebi -> case ebi of
            Left v -> return $ Left v
            Right v -> return $ Right v

        Nothing -> error ("[Refinement] No symbolic integer variable " ++ show n ++ " in " ++ show ls)

getSValPred ls (PNum i) = return $ Right $ literal i

getSValPred ls (PBool x) = if x then return $ Left sTrue else return $ Left sFalse



getModelExpr :: Type -> IO (Maybe Expr)
getModelExpr r@(RefinementType rname rtype ls (Just pred)) = runSMTWith z3 problem -- z3{verbose = True}

    where
        problem :: Symbolic (Maybe Expr)
        problem = do
            setTimeOut 300
            query $ do
                cs <- checkSat
                case cs of
                  Unk -> return Nothing
                  Unsat -> return Nothing
                  Sat -> do
                      -- TODO: very prone to deprecation :)
                      sendStringToSolver $ mparens $ "declare-fun " ++ rname ++ " " ++ mparens (unwords (map (\(RefinementType _ ty' _ _) -> show ty') ls)) ++ " " ++ show rtype
                      sendStringToSolver $ makeAxiomFromPredicate r
                      sendStringToSolver "(check-sat)"
                      s <- retrieveResponseFromSolver "*1" Nothing
                      let satres = last s
                      if satres == "sat" then do
                          sendStringToSolver "(get-model)"
                          s' <- retrieveResponseFromSolver "*2" Nothing
                          return $ Just $ parseSMTExpr $ concat s'
                      else if satres == "unsat" || satres == "unknown" then
                          return Nothing
                      else
                          error $ "[Refinements] Received weird response from the solver: " ++ show satres 


        makeAxiomFromPredicate :: Type -> String
        makeAxiomFromPredicate (RefinementType name rtype ls (Just pred)) =
            let predicateFormula = makePredicateString (null ls) (foldr (\(RefinementType _ _ _ mp) -> ((case mp of Nothing -> []; Just p -> [p]) ++)) [pred] ls) in
            if null ls then
                mparens ("assert " ++ predicateFormula)
            else
                mparens ("assert " ++
                    mparens ("forall " ++
                        mparens (unwords (map (\(RefinementType name' ty' _ _) -> mparens (name' ++ " " ++ show ty')) ls)) ++ " " ++ -- variables quantified universally
                    predicateFormula
                 ))


        makePredicateString :: Bool -> [Predicate] -> String
        makePredicateString _ [] = error "Shouldn't be making a predicate string from an empty list of predicates"
        makePredicateString hasNoArgs [PVar vname] = if vname == rname
                                              then (if hasNoArgs then id else mparens) $
                                                  vname ++ " " ++ unwords (map getRefName ls) -- Use function call instead of variable by itself
                                              else vname
        makePredicateString _ [PBool b] = if b then "true" else "false"
        makePredicateString _ [PNum i] = show i
        makePredicateString b [BinaryOp opn p1 p2] = let core = mparens $ getSMTLibName opn ++ " " ++ makePredicateString b [p1] ++ " " ++ makePredicateString b [p2] in
                                                       if opn == "!=" then mparens $ "not " ++ core
                                                                      else core
        makePredicateString b (p:xs) = mparens $ "=> " ++ makePredicateString b [p] ++ " " ++ makePredicateString b xs


        getSMTLibName :: String -> String
        getSMTLibName n
            | n == "==" = "="
            | n == "!=" = "=" -- a not is added in this case
            | n == "&&" = "and"
            | n == "||" = "or"
            | otherwise = n




parseSMTExpr :: String -> Expr
parseSMTExpr s = case runParser (contents $ parens pexpr) 0 "smt-exp-parse" s of
                Left x -> errorWithoutStackTrace $ "[Expr Parse] Failed: " ++ show x
                Right x -> x


pexpr :: Parser Expr
pexpr = parens $ do
    reserved "define-fun"
    name <- identifier
    args <- parens $ many pargument
    returnty <- tylit
    paexp


pargument :: Parser (Integer, Type)
pargument = parens $ do
    string "x!"
    i <- natural
    t <- tylit
    return (i, t)


paexp :: Parser Expr
paexp =  litexp
     <|> parens (do
             funname <- operator
             exps <- many1 paexp
             let exps' = if funname == "-" && length exps == 1    -- the subtraction might be a prefix meaning 0 - x
                            then Syntax.Lit (LitInt 0):exps
                            else exps
             return $ applyToParams (Syntax.ExpBop funname) exps')
    where
        -- assumes all available functions are binary
        applyToParams vf [] = error "[Refinements] Reached empty list"
        applyToParams vf [e] = e
        applyToParams vf (e:xs) = vf e (applyToParams vf xs)


litexp :: Parser Expr
litexp =  (Var . show <$> (string "x!" >> natural))
      <|> (Syntax.Lit . LitInt <$> natural)


operator :: Parser Name
operator =  (reservedOp "+" >> return "+")
        <|> (reservedOp "-" >> return "-")
        <|> (reservedOp "*" >> return "*")



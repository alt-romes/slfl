{-# LANGUAGE LambdaCase #-}
module Synth (synthAllType, synthType, synthMarks, synthMarksModule, synth) where

import Data.List
import Text.Read (readMaybe)
import qualified Data.Set as Set
import qualified Data.Map as Map
import Control.Applicative
import Control.Monad.Logic
import Control.Monad.State
import Control.Monad.Reader
import Data.Hashable
import Data.Maybe
import Data.Either
import Data.Bifunctor
import Debug.Trace
import Refinements


import CoreSyntax (Name, Type(..), Scheme(..), isInType, isExistentialType, isFunction)
import Syntax
import Program
import Util
import Constraints
import Minimize
import Typechecker (instantiateFrom)



type Gamma = [(Name, Either Scheme Type)] -- Unrestricted hypothesis              (Γ)
type Delta = [(Name, Type)]       -- Linear hypothesis (not left asynchronous)    (Δ)
type Omega = [(Name, Type)]       -- Ordered (linear?) hypothesis                 (Ω)
type Ctxt = (Subst, Restrictions, Gamma, Delta, Omega)   -- Delta out is a return value
type FocusCtxt = (Subst, Restrictions, Gamma, Delta)     -- Gamma, DeltaIn

-------------------------------------------------------------------------------
-- Synth "Monad"
-------------------------------------------------------------------------------

type Synth a = LogicT (StateT SynthState (ReaderT SynthReaderState IO)) a 


type SynthState = (MemoTable, Int)  -- (list of constraints added by the process to solve when instantiating a scheme, next index to instance a variable)
type MemoTable = Map.Map Int (Maybe (Expr, Delta, Subst, Int))


type SynthReaderState = ([ADTD], Int, [TraceTag], (Name, Bool), Int) -- (list of restrictions applied on types in specific places, list of ADTDs to be always present)
type Restriction = Either (Either Scheme Type, Type) Type
type Restrictions = [(RestrictTag, Restriction)]


data RestrictTag = ConstructADT | DeconstructADT | DecideLeftBangR deriving (Show, Eq, Ord)
instance Hashable RestrictTag where
    hashWithSalt a r = hashWithSalt a (show r)

data TraceTag = RightFun Ctxt Type | RightWith Ctxt Type | LeftTensor Ctxt Type Type | LeftUnit Ctxt Type | LeftPlus Ctxt Type Type | LeftSum Type Type | LeftADT Restrictions Ctxt Type Type | MoveLeftADT Restrictions Ctxt Type Type | LeftBang Ctxt Type Type | MoveToDelta (Name, Type) Type | Focus Restrictions Ctxt Type | DecideLeft Type Type | DecideRight Type | DecideLeftBang Restrictions Type Type | DecideLeftBangSch Restrictions Scheme Type | FocusLeftScheme (String, Type) FocusCtxt Type | RightTensor FocusCtxt Type | RightUnit FocusCtxt | RightPlus FocusCtxt Type | RightSum Type | RightADT Name Restrictions FocusCtxt Type | RightBang FocusCtxt Type | LeftFun FocusCtxt Type Type | LeftWith FocusCtxt Type Type | LeftExistentialTV | FocusLeftADT FocusCtxt Type Type | DefaultFocusLeft FocusCtxt (Name, Type) Type | DefaultFocusRight FocusCtxt Type | LeftRefinement Ctxt (Name, Type) Type | FocusLeftRefinement FocusCtxt (Name, Type) Type | RightRefinement FocusCtxt Type | FocusLeftBang FocusCtxt (Name, Type) Type | RightExistentialTV FocusCtxt (Name, Type) Type deriving (Show)


runSynth :: Int -> (Gamma, Delta) -> Type -> SynthState -> [ADTD] -> Int -> [Name] -> IO ([Expr], MemoTable)
runSynth n (g, d) t st adtds ed touse = do
    (exps_deltas, (memot, _)) <- runReaderT (runStateT (observeManyT n $ synthComplete (g, d, []) t) st) $ initSynthReaderState (case recf of {[] -> ""; ((n, _):_) -> n}) adtds ed
    return (map fst exps_deltas, memot)

    where
        synthComplete (g, d, o) t = do
            (e, d', _) <-  memoizesynth synth (Map.empty, [], recf, d, o) t -- synth only with the recursive function
                       <|> memoizesynth synth (Map.empty, [], g, d, o) t    -- synth with the whole context
            guard $ null d'
            guard $ synthResultUses touse e
            return (e, d')

        synthResultUses :: [Name] -> Expr -> Bool
        synthResultUses [] _ = True
        synthResultUses (x:xs) e = (Var x `isInExpr` e) && synthResultUses xs e

        recf = case g of
                 [] -> []
                 x:xs -> [x] -- head of Gamma is the recursive name since the recursive signature is the last added to the gamma context


initSynthState :: MemoTable -> Int -> SynthState
initSynthState mt i = (mt, i)


initSynthReaderState :: Name -> [ADTD] -> Int -> SynthReaderState
initSynthReaderState n a ed = (a, 0, [], (n, False), ed)





-------------------------------------------------------------------------------
-- Functions
-------------------------------------------------------------------------------

memoize :: Maybe (Maybe (Either (String, Scheme) (String, Type))) -> Ctxt -> Type -> Synth (Expr, Delta, Subst) -> Synth (Expr, Delta, Subst)
memoize maybefocus c@(cs,r,g,d,o) t syn = do -- TODO: Can possibly be improved/optimized if we look at the existential type vars and restrictions... perhaps the hash function can play a role in it...
    (memot, i) <- lift get
    let key = hash (map (second $ apply cs) r, map (apply cs . snd) g, map (apply cs . snd) d, map (apply cs . snd) o) + hash (apply cs t) + hash (apply cs ((bimap snd snd <$>) <$> maybefocus))
    case Map.lookup key memot of
       Nothing -> do        -- If this synth hasn't been previously done -- run it and save the resulting values and state
           ifte syn
             (\(e, d', cs') -> do
                 lift $ modify $ \(memot', i') -> (Map.insert key (Just (e, d', cs', i'-i)) memot', i')
                 return (e, d', cs'))
             (do lift $ put (Map.insert key Nothing memot, i)
                 empty)
       Just Nothing ->
           empty
           -- syn
       Just (Just (e, d', cs', deltai)) -> do 
           -- lift $ put (memot, i + deltai)
           -- return (e, d', cs') -- TODO: I think this has some issues with variable names that might collide
           -- TODO: This has major issues -- when enabled can't synth for example List (List Int) -o List In
           syn

memoizesynth :: (Ctxt -> Type -> Synth (Expr, Delta, Subst)) -> Ctxt -> Type -> Synth (Expr, Delta, Subst)
memoizesynth syn c ty = memoize Nothing c ty (syn c ty)

memoizefocus :: (FocusCtxt -> Type -> Synth (Expr, Delta, Subst)) -> FocusCtxt -> Type -> Synth (Expr, Delta, Subst)
memoizefocus synf c@(cs, r, g, d) ty = memoize Nothing (cs, r, g, d, []) ty (synf c ty)

memoizefocus' :: (Maybe (String, Type) -> FocusCtxt -> Type -> Synth (Expr, Delta, Subst)) -> Maybe (String, Type) -> FocusCtxt -> Type -> Synth (Expr, Delta, Subst)
memoizefocus' syn fty c@(cs, r, g, d) ty = memoize (Just (Right <$> fty)) (cs, r, g, d, []) ty (syn fty c ty)

memoizefocusSch :: ((String, Scheme) -> FocusCtxt -> Type -> Synth (Expr, Delta, Subst)) -> (String, Scheme) -> FocusCtxt -> Type -> Synth (Expr, Delta, Subst)
memoizefocusSch syn fty c@(cs, r, g, d) ty = memoize (Just (Just (Left fty))) (cs, r, g, d, []) ty (syn fty c ty)


allowrecursion :: Synth a -> Synth a
allowrecursion = local (\(b,c,d,(fn, _),ed) -> (b,c,d,(fn, True),ed))


addconstraint :: Subst -> Constraint -> Synth Subst
addconstraint subs c = do
    let maybesubs = solveconstraintsExistential subs c
    guard $ isJust maybesubs
    return $ fromJust maybesubs


addrestriction :: RestrictTag -> Type -> Restrictions -> Restrictions
addrestriction tag ty rs = (tag, Right ty):rs


addbinaryrestriction :: RestrictTag -> Either Scheme Type -> Type -> Restrictions -> Restrictions
addbinaryrestriction tag ty ty' rs = if isFunction ty then (tag, Left (ty, ty')):rs else rs


addtrace :: TraceTag -> Synth a -> Synth a
addtrace t s = do
    (tstck, depth) <- gettracestack
    -- trace ("D" ++ show depth ++ ": " ++ show t) $ -- ++ "\n-- stack --\n" ++ unlines (map show tstck) ++ "\n") $
    local (\(b,c,d,e,f) -> (b,c+1,t:d,e,f)) s


gettracestack :: Synth ([TraceTag], Int)
gettracestack = lift (lift ask) >>= \(b,c,d,e,f) -> return (d,c)


getdepth :: Synth Int
getdepth = lift (lift ask) >>= \(b,c,d,e,f) -> return c


getRecInfo :: Synth (Name, Bool)
getRecInfo = lift (lift ask) >>= \(b,c,d,ra,f) -> return ra


getExistentialDepth :: Synth Int
getExistentialDepth = lift (lift ask) >>= \(b,c,d,ra,ed) -> return ed


checkrestrictions :: RestrictTag -> Type -> Restrictions -> Bool
checkrestrictions tag ty@(ADT tyn tpl) rs = -- Restrictions only on ADT Construction and Destruction
    let reslist = rights $ map snd $ filter (\(n,x) -> n == tag) rs in
    ty `notElem` reslist -- && (not (isExistentialType ty) || not (any isExistentialType $ filter (\(ADT tyn' _) -> tyn == tyn') reslist))

checkbinaryrestrictions :: RestrictTag -> (Either Scheme Type, Type) -> Restrictions -> Synth Bool
checkbinaryrestrictions tag typair rs = do
    existentialdepth <- getExistentialDepth
    let reslist = lefts $ map snd $ filter (\(n,x) -> n == tag) rs
    return $ typair `notElem` reslist &&
        -- isExistential => Poly-Exist pairs are less than the existential depth
        (not (isExistentialType $ snd typair) || existentialdepth > count True (map (\x -> isExistentialType (snd x) && isLeft (fst x)) reslist)) -- no repeated use of unr functions or use of unr func when one was used focused on an existential


getadtcons :: Type -> Synth [(Name, Type)] -- Handles substitution of polimorfic types with actual type in constructors
getadtcons (ADT tyn tps) = do
    adtds <- lift (lift ask) >>= \(b,c,d,e,f) -> return b
    case find (\(ADTD name ps _) -> tyn == name && length tps == length ps) adtds of
      Just (ADTD _ paramvars cons) ->
          let subst = Map.fromList $ zip paramvars tps in
          return $ map (apply subst) cons
      Nothing -> return []


fresh :: Synth String
fresh = do 
    (m, n) <- lift get
    lift $ put (m, n+1)
    return $ getName n


freshIndex :: Synth Int
freshIndex = do 
    (m, n) <- lift get
    lift $ put (m, n+1)
    return n


assertADTHasCons :: Type -> Synth Bool
assertADTHasCons t =
    case t of
       ADT name _ -> do
           cons <- getadtcons t
           return $ not $ null cons
       _        ->
           return True


findType :: Type -> Delta -> Bool
findType t d = t `elem` map snd d


isAtomic :: Type -> Bool
isAtomic t =
    case t of
       TyLit _              -> True
       TypeVar _            -> True
       _                    -> False


---- subsitute var n with expn in expf
substitute :: String -> Expr -> Expr -> Expr
substitute n expn = transform (\case
                                v@(Var x) -> if x == n then expn else v
                                x -> x)


-- TODO: Make Generic and move to constraints?
ftvctx :: FocusCtxt -> Set.Set Int
ftvctx = ftvctx' Set.empty
    where
        ftvctx' :: Set.Set Int -> FocusCtxt -> Set.Set Int
        ftvctx' acc (_, _, gc, dc) = Set.unions (map (ftvctx'' . snd) gc) `Set.union` Set.unions (map (ftv . snd) dc)
        ftvctx'' = \case {Right t -> ftv t; Left sch -> ftvsch sch}
        ftvsch (Forall ns t) = Set.difference (Set.fromList ns) $ ftv t


-- TODO: Make Generic and move to constraints?
generalize :: FocusCtxt -> Type -> Scheme
generalize ctxt t = Forall ns t 
    where ns = Set.toList $ Set.difference (ftv t) (ftvctx ctxt)


isRecursiveType :: Type -> Synth Bool
isRecursiveType (ADT tyn tps) = do
    adtds <- getadtcons (ADT tyn tps)
    return $ any (\(_, ty) -> ADT tyn tps `isInType` ty) adtds




-------------------------------------------------------------------------------
-- Main Logic
-------------------------------------------------------------------------------

synth :: Ctxt -> Type -> Synth (Expr, Delta, Subst)

---- * Right asynchronous rules * -----------------

---- -oR
synth c@(cs, rs, г, d, o) (Fun a b) = addtrace (RightFun c (Fun a b)) $ do
    name <- fresh
    let b' = if isRefType a
                then addRefinementToCtxs a b    -- Everytime we decompose a dependent function, we must add it to the rest's refinement context... we need to change the core rules for this...
                else b
    (exp, d', cs') <- memoizesynth synth (cs, rs, г, d, o ++ [(name, a)]) b' -- TODO:! Não usar append ?
    guard (name `notElem` map fst d')
    return (Abs name (Just a) exp, d', cs')

---- &R
synth c@(cs, rs, g, d, o) (With a b) = addtrace (RightWith c (With a b)) $ do
    (expa, d', cs') <- memoizesynth synth c a
    (expb, d'', cs'') <- memoizesynth synth (cs', rs, g, d, o) b
    guard (d' == d'')
    return (WithValue expa expb, d', cs'')

-- no more synchronous right propositions, start inverting the ordered context (Ω)



---- * Left asynchronous rules * ------------------

---- *L
synth c@(cs, rs, g, d, (n, Tensor a b):o) t = addtrace (LeftTensor c (Tensor a b) t) $ do
    n1 <- fresh
    n2 <- fresh
    (expt, d', cs') <- memoizesynth synth (cs, rs, g, d, (n2, b):(n1, a):o) t
    guard ((n1 `notElem` map fst d') && (n2 `notElem` map fst d'))
    return (LetTensor n1 n2 (Var n) expt, d', cs')

---- 1L
synth c@(cs, rs, g, d, (n, Unit):o) t = addtrace (LeftUnit c t) $ do
    (expt, d', cs') <- memoizesynth synth (cs, rs, g, d, o) t
    return (LetUnit (Var n) expt, d', cs')

---- +L
synth c@(cs, rs, g, d, (n, Plus a b):o) t = addtrace (LeftPlus c (Plus a b) t) $ do
    n1 <- fresh
    n2 <- fresh
    (expa, d', cs') <- memoizesynth synth (cs, rs, g, d, (n1, a):o) t
    (expb, d'', cs'')  <- memoizesynth synth (cs', rs, g, d, (n2, b):o) t
    guard (d' == d'')
    guard ((n1 `notElem` map fst d') && (n2 `notElem` map fst d''))
    return (CaseOfPlus (Var n) n1 expa n2 expb, d', cs'')

---- sumL
synth (cs, rs, g, d, (n, Sum tys):o) t = addtrace (LeftSum (Sum tys) t) $ do
    (ls, cs'') <- runStateT (mapM (\(name, ct) -> do
        varid <- lift fresh
        cs' <- get
        (exp, d', cs'') <- lift $ memoizesynth synth (cs', rs, g, d, (varid, ct):o) t
        guard $ varid `notElem` map fst d'
        put cs''
        return (name, varid, exp, d')
        ) tys) cs
    let (n1, varid1, e1, d1') = head ls
    guard $ all ((== d1') . (\(_,_,_,c) -> c)) (tail ls)
    return (CaseOfSum (Var n) (map (\(n,i,e,_) -> (n,i,e)) ls), d1', cs'')

---- adtL
synth c@(cs, rs, g, d, p@(n, ADT tyn tps):o) t = addtrace (LeftADT rs c (ADT tyn tps) t) (do
    guard $ checkrestrictions DeconstructADT (ADT tyn tps) rs
    adtds <- getadtcons (ADT tyn tps)
    if null adtds
       then let rs' = addrestriction DeconstructADT (ADT tyn tps) rs in memoizesynth synth (cs, rs', g, p:d, o) t    -- An ADT that has no constructors might still be used to instantiate a proposition, but shouldn't leave synchronous mode (hence the restriction)
       else do
            isrectype <- isRecursiveType (ADT tyn tps)
            (ls, cs'') <- runStateT (mapMFairConj (\(name, vtype) ->
                let rs' = if isrectype then addrestriction DeconstructADT (ADT tyn tps) rs else rs in   -- For recursive types, restrict deconstruction of this type in further computations
                        case vtype of
                          Unit -> do
                            cs' <- get
                            (exp, d', cs'') <- lift $ memoizesynth synth (cs', rs', g, d, o) t
                            put cs''
                            return (name, "", exp, d')
                          argty -> do -- only allow recursion after having deconstructed a recursive ADT
                            varid <- lift fresh
                            cs' <- get
                            (exp, d', cs'') <- lift $ (if isrectype then allowrecursion else id)
                                                    $ memoizesynth synth (cs', rs', g, d, (varid, argty):o) t
                            put cs''
                            guard $ varid `notElem` map fst d'
                            return (name, varid, exp, d')
                ) adtds) cs
            let (n1, varid1, e1, d1') = head ls
            guard $ all ((== d1') . (\(_,_,_,c) -> c)) (tail ls) -- all resulting contexts are the same
            return (CaseOf (Var n) (map (\(n, vari, exp, _) -> (n, vari, exp)) ls), d1', cs'')
    ) <|>
    addtrace (MoveLeftADT rs c (ADT tyn tps) t) (do
    guard $ not $ checkrestrictions DeconstructADT (ADT tyn tps) rs                 -- ADT with a restriction on deconstruction might still be useful by being instantiated while focused -- e.g. a Tensor was deconstructed asynchronously but the ADT has a deconstruct restriction -- it shouldn't fail, yet it shouldn't deconstruct either -- this option covers that case (Similar to "Move To Delta" but for ADTs that we cannot deconstruct any further)
    memoizesynth synth (cs, rs, g, p:d, o) t)                                       -- So if we failed above because a restriction didn't allow us to invert this ADT, try using the hypothesis in the linear context -- it won't loop back here because the DeconstructADT
        where
            mapMFairConj _ [] = return [] 
            mapMFairConj f (x:xs) =
                f x >>- \x' -> do
                    xs' <- mapMFairConj f xs
                    return $ x':xs'

---- !L
synth c@(cs, rs, g, d, (n, Bang a):o) t = addtrace (LeftBang c (Bang a) t) $ do
    nname <- fresh
    (exp, d', cs') <- memoizesynth synth (cs, rs, (nname, Right a):g, d, o) t
    guard (nname `notElem` map fst d') -- TODO: Useless?
    return (LetBang nname (Var n) exp, d', cs')

---- refinementL
-- not used because we add the refinements to the context in the RightFunction rule
-- synth c@(g, d, rn@(n, r@RefinementType {}):o) t = addtrace (LeftRefinement c rn t) $ do
--     -- let t' = addRefinementToCtxs r t    -- Add this refinement to the context of refinement types in t
--     -- let d' = map (second (addRefinementToCtxs r)) d -- TODO: Either add this type to all linear context, or add to the goal when inverting the function, not only when moving to delta - but that would contaminate the rules :P
       -- synth (g, rn:d, o) t


---- * Synchronous left propositions to Δ * -------

synth (cs, rs, g, d, p:o) t =
    addtrace (MoveToDelta p t) $ memoizesynth synth (cs, rs, g, p:d, o) t



---- * Synchronous rules * -------------------------

-- no more asynchronous propositions, focus

synth c@(cs, rs, g, d, []) t = addtrace (Focus rs c t) $
    memoizefocus focus (cs, rs, g, d) t


focus :: FocusCtxt -> Type -> Synth (Expr, Delta, Subst)
focus c goal =
    decideLeft c goal <|> decideRight c goal <|> decideLeftBang c goal -- deciding left before right will be correct more often than not (at least based on recent attempts...) -- !TODO: Deciding Right before Left can lead to infinite loops!! (Ex: Expr = Var Nat | Lam Expr)

    where
        decideRight, decideLeft, decideLeftBang :: FocusCtxt -> Type -> Synth (Expr, Delta, Subst)

        decideRight c goal = addtrace (DecideRight goal) $
            if isAtomic goal                            -- to decide right, goal cannot be atomic
                then empty
                else do
                    assertADTHasCons goal >>= guard     -- to decide right, goal cannot be an ADT that has no constructors
                    memoizefocus' focus' Nothing c goal


        decideLeft (cs, rs, g, din) goal =
            case din of
              []     -> empty
              _ -> foldr ((<|>) . (\nx@(n,x) -> addtrace (DecideLeft x goal) $ memoizefocus' focus' (Just nx) (cs, rs, g, delete nx din) goal)) empty din


        decideLeftBang c@(cs, rs, g, din) goal =
            case g of
              []   -> empty
              _ -> do
                  foldr ((<|>) . (\case
                                    (n, Right x) -> addtrace (DecideLeftBang rs x goal) $ do
                                        rs' <- managerestrictions n (Right x)
                                        memoizefocus' focus' (Just (n, x)) (cs, rs', g, din) goal;
                                    (n, Left sch) -> addtrace (DecideLeftBangSch rs sch goal) $ do
                                        rs' <- managerestrictions n (Left sch)
                                        memoizefocusSch focusSch (n, sch) (cs, rs', g, din) goal)) empty g
                                 where
                                     managerestrictions :: Name -> Either Scheme Type -> Synth Restrictions
                                     managerestrictions n x = do    
                                         (recname, recallowed) <- getRecInfo  -- Restrict usage of recursive function if it isn't allowed
                                         guard $ recname /= n || recallowed
                                         checkbinaryrestrictions DecideLeftBangR (x, goal) rs >>= guard -- Restrict re-usage of decide left bang to synth the same goal a second time, if using a function
                                         return $ addbinaryrestriction DecideLeftBangR x goal rs

        
            
        ---- Eliminating Schemes
        focusSch :: (String, Scheme) -> FocusCtxt -> Type -> Synth (Expr, Delta, Subst)

        ---- VL
        focusSch (n, sch@(Forall ns t)) ctxt@(cs, rs, g, din) goal = do
            (et, etvars) <- existencialInstantiate sch                                              -- tipo com existenciais
            addtrace (FocusLeftScheme (n, et) ctxt goal) $ do
                -- can only try scheme if current constraints are still safe
                -- before trying to synth Unit to use as the instanciation of an existential ?x, make sure this new constraint doesn't violate previous constraints,
                -- or else we might try to synth Unit assuming ?x again, which will fail solving the constraints, which in turn will make the Unit try to be synthed again using the other choice which is to assume ?x again...
                -- (et, etvars) <- existencialInstantiate sch                                       -- tipo com existenciais
                (se, d', cs') <- memoizefocus' focus' (Just (n, et)) ctxt goal                      -- fail ou success c restrições -- sempre que é adicionada uma constraint é feita a unificação
                                                                                                    -- resolve ou falha -- por conflito ou falta informação
                -- trace ("DID I INSTANCE ALL VARIABLES " ++ show (apply cs' et) ++ "\nftv:" ++ show (ftv $ apply cs' et) ++ "\nSet etvars:" ++ show (Set.fromList etvars) ++ "? " ++ show (Set.disjoint (Set.fromList etvars) (ftv $ apply cs' et))) $ do
                                                                                                    -- por conflicto durante o processo
                guard (Set.disjoint (Set.fromList etvars) (ftv $ apply cs' et))                     -- por falta de informação (não pode haver variáveis existenciais bound que fiquem por instanciar, i.e. não pode haver bound vars nas ftvs do tipo substituido)
                                                                                                    -- after making sure no instantiated variables escaped, the constraints added to the substitution can be forgotten so that it doesn't complicate further scheme computations
                return (se, d', cs')                                                                -- if constraints are "total" and satisfiable, the synth using a polymorphic type was successful
                    where
                        existencialInstantiate (Forall ns t) = do
                            netvs <- mapM (const $ do {i <- freshIndex; return (ExistentialTypeVar i, -i)}) ns
                            return (apply (Map.fromList $ zip ns $ map fst netvs) t, map snd netvs)



        focus' :: Maybe (String, Type) -> FocusCtxt -> Type -> Synth (Expr, Delta, Subst)

        ---- * Right synchronous rules * ------------------

        ---- *R
        focus' Nothing c@(cs, rs, g, d) (Tensor a b) = addtrace (RightTensor c (Tensor a b)) $ do
            (expa, d', cs') <- case a of { ADT _ _ -> memoizefocus focus c a; _ -> memoizefocus' focus' Nothing c a }
            (expb, d'', cs'') <- case b of { ADT _ _ -> memoizefocus focus (cs', rs, g, d') b; _ -> memoizefocus' focus' Nothing (cs', rs, g, d') b }
            return (TensorValue expa expb, d'', cs'')

        ---- 1R
        focus' Nothing c@(cs, _, _, d) Unit = addtrace (RightUnit c) $
            return (UnitValue, d, cs)
            
        ---- +R
        focus' Nothing c (Plus a b) = addtrace (RightPlus c (Plus a b)) $ do
            (il, d', cs') <- case a of { ADT _ _ -> memoizefocus focus c a; _ -> memoizefocus' focus' Nothing c a }
            return (InjL (Just b) il, d', cs')
            `interleave` do
            (ir, d', cs') <- case b of { ADT _ _ -> memoizefocus focus c b; _ -> memoizefocus' focus' Nothing c b }
            return (InjR (Just a) ir, d', cs')

        ---- sumR
        focus' Nothing c (Sum sts) = addtrace (RightSum (Sum sts)) $
            foldr (interleave . (\(tag, goalt) ->
                do
                   (e, d', cs') <- case goalt of { ADT _ _ -> memoizefocus focus c goalt; _ -> memoizefocus' focus' Nothing c goalt }
                   let smts = map (second Just) $ delete (tag, goalt) sts
                   return (SumValue smts (tag, e), d', cs')
                )) empty sts

        ---- adtR
        focus' Nothing c@(cs, rs, g, d) (ADT tyn pts) = do
            cons <- getadtcons (ADT tyn pts)
            foldr (interleave . (\(tag, argty) ->
                addtrace (RightADT tag rs c (ADT tyn pts)) $
                   case argty of
                     Unit -> return (Var tag, d, cs)        -- The branch where this constructor is used might fail later e.g. if an hypothesis isn't consumed from delta when it should have
                     argtype -> do
                         -- rs <- lift (lift ask) >>= \(a,b,c,d,e) -> return a
                         -- let reslist = rights $ map snd $ filter (\(n,x) -> n == ConstructADT) rs
                         guard $ checkrestrictions ConstructADT (ADT tyn pts) rs
                         -- trace ("Check if " ++ show (ADT tyn pts) ++ " is not restricted by " ++ show reslist ++ " in " ++ show rs ++ " : " ++ show b ++ "? ?? " ++ show res) $ checkrestrictions' res ConstructADT (ADT tyn pts) >>= guard     -- Assert this ADT's construction isn't restricted
                         if case argtype of
                                ADT tyn' pts' -> tyn == tyn' && pts == pts'         -- If the constructor for an ADT takes itself as a parameter, focus right should fail and instead focus left. -- TODO: Questionable
                                _ -> False
                            then empty
                            else do
                                let rs' = addrestriction ConstructADT (ADT tyn pts) rs     -- Cannot construct ADT t as means to construct ADT t -- might cause an infinite loop
                                (arge, d', cs') <- case argtype of { ADT _ _ -> memoizefocus focus (cs, rs', g, d) argtype; _ -> memoizefocus' focus' Nothing (cs, rs', g, d) argtype }
                                return (App (Var tag) arge, d', cs')
                )) empty cons
            -- When we're right focused, we might continue right focused as we construct the proof (e.g. RightTensor),
            -- However, where other propositions would loop back to asynch mode, and back again to the decision point,
            -- Allowing for a left decision and an eventual instantiation of the goal,
            -- A restricted ADT might fail right away while being right focused, and never considered the possibility of deciding left to instantiate it
            -- Knowning so, all `focus right` expressions will instead just `focus` (and `decide`) on algebraic data types (ADT)s
           

        ---- !R
        focus' Nothing c@(cs, rs, g, d) (Bang a) = addtrace (RightBang c (Bang a)) $ do
            (expa, d', cs') <- memoizesynth synth (cs, rs, g, d, []) a
            guard (d == d')
            return (BangValue expa, d', cs')


        ---- refinementR
        focus' Nothing c@(cs, rs, g, d) r@(RefinementType rname ty rctx mpred) = addtrace (RightRefinement c r) $
            case mpred of
              Nothing -> focus' Nothing c ty    -- If there's no predicate try instancing the type
              Just pred -> do
                  model <- liftIO $ getModelExpr r
                  case model of
                    Nothing -> empty   -- the SMT solver couldn't generate a model for this predicate
                    Just expr -> do -- error ("Got model " ++ show expr ++ " and " ++ show rctx ++ " and now utilizing variables to instance it")
                        (expr', d') <- ifte (replaceRefVariables expr) return (trace ("Failed to instance expression from the SMT Solver: " ++ show expr) empty)
                        return (expr', d', cs)

            where
                replaceRefVariables :: Expr -> Synth (Expr, Delta)
                replaceRefVariables e = maybe empty return $ runStateT (transformM replaceTransform e) d
                
                replaceTransform :: Expr -> (StateT Delta) Maybe Expr
                replaceTransform (Var name) =
                    case readMaybe name :: Maybe Int of -- The variable might be a function like "add", it isn't necessarily a placeholder number
                        Nothing -> return $ Var name
                        Just _ -> Var <$> findVarName name
                replaceTransform e = return e

                findVarName :: Name -> (StateT Delta) Maybe String
                findVarName name = do
                    let refname = getRefName $ rctx !! read name
                    delta <- get
                    case find ((refname ==) . getRefName . snd) delta of
                      Just (vname, ft) -> do
                          put $ delete (vname, ft) delta        -- !!!TODO: there is no alternative for choosing the variables to instantiate the type synthetised by the SMT, there's no backtracking, we always try to find in delta first and will always instantiate one when available
                          return vname 
                      Nothing ->
                          case find ((\case
                                        Left (Forall _ (RefinementType n' _ _ _)) -> n' == name
                                        Left (Forall _ _) -> False
                                        Right (RefinementType n' _ _ _) -> n' == name
                                        Right _ -> False
                                     ) . snd) g of
                            Just (vname, _) -> return vname
                            Nothing -> empty



        ---- * Left synchronous rules * -------------------

        ---- -oL
        focus' (Just (n, Fun a b)) c@(cs, rs, g, d) goal = addtrace (LeftFun c (Fun a b) goal) $ do
            nname <- fresh
            let b' = if isRefType a
                        then addRefinementToCtxs a b    -- Everytime we decompose a dependent function, we must add it to the rest's refinement context... we need to change the core rules for this...
                        else b
            (expb, d', cs') <- memoizefocus' focus' (Just (nname, b')) c goal
            (expa, d'', cs'') <- memoizesynth synth (cs', rs, g, d', []) a
            return (substitute nname (App (Var n) expa) expb, d'', cs'')
            
        ---- &L
        focus' (Just (n, With a b)) c goal = addtrace (LeftWith c (With a b) goal) $
            do
                nname <- fresh
                (lf, d', cs') <- memoizefocus' focus' (Just (nname, a)) c goal
                return (substitute nname (Fst (Var n)) lf, d', cs')
            <|>
            do
                nname <- fresh
                (rt, d', cs') <- memoizefocus' focus' (Just (nname, b)) c goal
                return (substitute nname (Snd (Var n)) rt, d', cs')

        ---- ∃L (?)
        focus' (Just (n, ExistentialTypeVar x)) (cs, rs, g, d) goal = addtrace LeftExistentialTV $
            case goal of
              (ExistentialTypeVar y) ->
                  if x == y then return (Var n, d, cs)          -- ?a |- ?a succeeds
                            else empty                      -- ?a |- ?b fails
              _ -> do                                       -- ?a |- t  succeeds with constraint
                  cs' <- addconstraint cs $ Constraint (ExistentialTypeVar x) goal
                  return (Var n, d, cs')


        ---- * Proposition no longer synchronous * --------

        
        focus' (Just nh@(n, Bang t)) c (Bang goal) = addtrace (FocusLeftBang c nh (Bang goal)) $ -- If we have a bang focused on bang, don't loop through focus and left bang --> might fail synthesis because of restrictions and is unnecessary
            focus' (Just (n, t)) c goal


        -- preemptively instance existential tv goals
        focus' (Just nh@(n, h)) c@(cs, rs, g, d) (ExistentialTypeVar x) = addtrace (RightExistentialTV c nh (ExistentialTypeVar x)) $ do
            cs' <- addconstraint cs $ Constraint (ExistentialTypeVar x) h -- goal is an existential proposition generate a constraint and succeed
            return (Var n, d, cs')


        ---- adtLFocus
        ---- if we're focusing left on an ADT X while trying to synth ADT X, instead of decomposing the ADT as we do when inverting rules, we'll instance the var right away -- to tame recursive types
        focus' (Just nh@(n, ADT tyn tps)) c@(cs, rs, g, d) goal = addtrace (FocusLeftADT c (ADT tyn tps) goal) $
            if case goal of
                 ADT tyn' tps' -> tyn' == tyn
                 _ -> False
              then do
                  let (ADT tyn' tps') = goal
                  cs' <- addconstraint cs $ Constraint (ADT tyn tps) (ADT tyn' tps')
                  return (Var n, d, cs')
              else do
                  adtcns <- getadtcons (ADT tyn tps) 
                  guard $ not $ null adtcns                                 -- If the type can't be desconstructed fail here, trying it asynchronously will force another focus/decision of goal -- which under certain circumstances causes an infinite loop
                  guard $ checkrestrictions DeconstructADT (ADT tyn tps) rs -- Assert ADT to move to omega can be deconstructed. ADTs that can't would loop back here if they were to be placed in omega
                  memoizesynth synth (cs, rs, g, d, [nh]) goal


        ---- refinementLFocus
        focus' (Just nh@(n, r@(RefinementType rname ty rctx mpred))) c@(cs, rs, g, d) goal = addtrace (FocusLeftRefinement c nh goal) $
            case goal of
              RefinementType _ _ ls goalpred ->
                  case goalpred of
                    Nothing -> focus' (Just (n, ty)) c goal    -- whatever requirement can instance non-requirement
                    Just _ -> do                               -- using proposition to instance a refinement type requires extra logic
                        guard $ not $ isJust mpred && isNothing goalpred
                        guard $ length ls == length rctx               -- no way to instanciating refinements that have different number of variables : TODO OK?
                        satunify <- liftIO $ satunifyrefinements r goal     -- we need to make sure it satisfy all constraints
                        guard satunify
                        return (Var n, d, cs)
              _ -> focus' (Just (n, ty)) c goal -- using the focus proposition to instance any other type is the same as using the type without the refinements


        ---- left focus is either atomic or not.
        ---- if it is atomic, it'll either be the goal and instanciate it, or fail
        ---- if it's not atomic, and it's not left synchronous, unfocus

        focus' (Just nh@(n, h)) c@(cs, rs, g, d) goal
          | isAtomic h                      -- left focus is atomic
          = addtrace (DefaultFocusLeft c nh goal) $ do
                guard (h == goal)      -- if is atomic and not the goal, fail
                return (Var n, d, cs)  -- else, instantiate it
          | otherwise
          = addtrace (DefaultFocusLeft c nh goal) $ memoizesynth synth (cs, rs, g, d, [nh]) goal         -- left focus is not atomic and not left synchronous, unfocus



        focus' Nothing c (ExistentialTypeVar _) = empty

        ---- right focus is not synchronous, unfocus.

        focus' Nothing c@(cs, rs, g, d) goal = addtrace (DefaultFocusRight c goal) $
            memoizesynth synth (cs, rs, g, d, []) goal





-------------------------------------------------------------------------------
-- Functions
-------------------------------------------------------------------------------

removeadtcons :: [ADTD] -> (Gamma, Delta) -> (Gamma, Delta)
removeadtcons adts (fc, bc) = case adts of -- During the synth process, constructors should only be used when focused right on the ADT -- so remove them from the unrestricted context
    [] -> (fc, bc)
    (ADTD _ _ cons):xs -> removeadtcons xs (filter (\(n, _) -> isNothing $ lookup n cons) fc, bc)


synthCtxAllType :: Int -> MemoTable -> (Gamma, Delta) -> Int -> [ADTD] -> Type -> Int -> [Name] -> IO ([Expr], MemoTable)
synthCtxAllType n mt c i adts t ed touse = do
    let c' = removeadtcons adts c
    (exps, memot) <- runSynth n c' t (initSynthState mt i) adts ed touse
    if null exps
        then error $ "[Synth] Failed synthesis of: " ++ show t
        else return (exps, memot)


synthCtxType :: MemoTable -> (Gamma, Delta) -> Int -> [ADTD] -> Type -> Int -> [Name] -> IO (Expr, MemoTable)
synthCtxType mt c i adts t ed touse = do
    (exps, memot) <- synthCtxAllType 1 mt c i adts t ed touse
    return (head exps, memot)




-------------------------------------------------------------------------------
-- Exported Functions
-------------------------------------------------------------------------------

synthAllType :: Type -> IO [Expr]
synthAllType t = fst <$> synthCtxAllType 5 Map.empty ([], []) 0 [] t 0 [] -- Not really *all* bc runSynth might loop forever?


synthType :: Type -> IO Expr
synthType t = head <$> synthAllType (instantiateFrom 0 $ generalize (Map.empty, [], [], []) t)


synthMarks :: Expr -> [ADTD] -> (StateT MemoTable IO) Expr -- replace all placeholders in an expression with a synthetized expr
synthMarks ex adts = transformM transformfunc ex
    where
        transformfunc :: Expr -> (StateT MemoTable IO) Expr
        transformfunc =
            \case
                (Mark _ name c@(fc, bc) t (ed, touse)) -> do
                    mt <- get
                    let sch@(Forall tvs t') = fromMaybe (error "[Synth] Failed: Marks can't be synthetized without a type.") t
                    case name of
                      Nothing    -> do -- Non-recursive Mark
                        (exp, memot') <- liftIO $ synthCtxType mt c (length tvs) adts (instantiateFrom 0 sch) ed touse
                        modify (`Map.union` memot')
                        return exp
                      Just name' -> -- Recursive Mark
                        case t' of
                          Fun (ADT tyn tps) t2 ->
                              let adtcons = concatMap (\(ADTD _ _ cs) -> cs) $ filter (\(ADTD name _ _) -> tyn == name) adts in
                              let i = length tvs in do
                                  branches <- synthBranches adtcons (i+1)
                                  return $ Abs (getName i) (Just (ADT tyn tps)) $ CaseOf (Var (getName i)) branches
                              where
                                  synthBranches :: [(Name, Type)] -> Int -> (StateT MemoTable IO) [(String, String, Expr)]
                                  synthBranches adtcons i = mapM (\(name, vtype) ->
                                        case vtype of
                                          Unit -> do
                                              (exp, memot') <- liftIO $ synthCtxType mt c i adts t2 0 []
                                              modify (`Map.union` memot')
                                              return (name, "", exp)
                                          argty -> do
                                              (exp, memot') <- liftIO $ synthCtxType mt ((name', Left sch):fc, (getName i, argty):(name', instantiateFrom 0 sch):bc) (i+1) adts t2 ed touse
                                              modify (`Map.union` memot')
                                              return (name, getName i, exp) -- TODO: Inverter ordem fun - hyp ou hyp - fun em delta? vai definir qual é tentado primeiro
                                      ) adtcons
                          _ ->
                              error "[Synth Mark] Recursive mark must be of type ADT a -> b"
                x -> return x
                           


-- pre: program has been type inferred
synthMarksModule :: Program -> IO Program
synthMarksModule (Program adts bs ts cs) = do
    synthbs <- synthMarksModule' Map.empty bs
    return $ minimize $ Program adts synthbs ts cs
    where
        synthMarksModule' :: MemoTable -> [Binding] -> IO [Binding]
        synthMarksModule' _ [] = return []
        synthMarksModule' memot ((Binding n e):xs) = do
            (syne, memot') <- runStateT (synthMarks e adts) memot
            (Binding n syne :) <$> synthMarksModule' memot' xs


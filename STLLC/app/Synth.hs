{-# LANGUAGE LambdaCase #-}
module Synth (synthAllType, synthType, synthMarks, synthMarksModule, synth) where

import Data.List
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


import CoreSyntax (Name, Type(..), Scheme(..), isInType, isExistentialType)
import Syntax
import Program
import Util
import Constraints
import Minimize
import Typechecker (instantiateFrom)



type Gamma = [(Name, Either Scheme Type)] -- Unrestricted hypothesis              (Γ)
type Delta = [(Name, Type)]       -- Linear hypothesis (not left asynchronous)    (Δ)
type Omega = [(Name, Type)]       -- Ordered (linear?) hypothesis                 (Ω)
type Ctxt = (Gamma, Delta, Omega)   -- Delta out is a return value
type FocusCtxt = (Gamma, Delta)     -- Gamma, DeltaIn

-------------------------------------------------------------------------------
-- Synth "Monad"
-------------------------------------------------------------------------------

type Synth a = LogicT (StateT SynthState (ReaderT SynthReaderState IO)) a 


type SynthState = (MemoTable, Subst, Int)  -- (list of constraints added by the process to solve when instantiating a scheme, next index to instance a variable)
type MemoTable = Map.Map Int (Maybe (Expr, Delta, Subst, Int))


type SynthReaderState = (Restrictions, [ADTD], Int, [TraceTag], Name) -- (list of restrictions applied on types in specific places, list of ADTDs to be always present)
type Restriction = Either (Type, Type) Type
type Restrictions = [(RestrictTag, Restriction)]


data RestrictTag = ConstructADT | DeconstructADT | DecideLeftBangR deriving (Show, Eq)
instance Hashable RestrictTag where
    hashWithSalt a r = hashWithSalt a (show r)

data TraceTag = RightFun Ctxt Type | RightWith Ctxt Type | LeftTensor Ctxt Type Type | LeftUnit Ctxt Type | LeftPlus Ctxt Type Type | LeftSum Type Type | LeftADT Restrictions Ctxt Type Type | MoveLeftADT Restrictions Ctxt Type Type | LeftBang Ctxt Type Type | MoveToDelta (Name, Type) Type | Focus Restrictions Ctxt Type | DecideLeft Type Type | DecideRight Type | DecideLeftBang Restrictions Type Type | DecideLeftBangSch Restrictions Scheme Type | FocusLeftScheme (String, Type) FocusCtxt Type | RightTensor FocusCtxt Type | RightUnit FocusCtxt | RightPlus FocusCtxt Type | RightSum Type | RightADT Name Restrictions FocusCtxt Type | RightBang FocusCtxt Type | LeftFun FocusCtxt Type Type | LeftWith FocusCtxt Type Type | LeftExistentialTV | FocusLeftADT FocusCtxt Type Type | DefaultFocusLeft FocusCtxt (Name, Type) Type | DefaultFocusRight FocusCtxt Type | LeftRefinement Ctxt (Name, Type) Type | FocusLeftRefinement FocusCtxt (Name, Type) Type | RightRefinement FocusCtxt Type deriving (Show)


runSynth :: Int -> (Gamma, Delta) -> Type -> SynthState -> [ADTD] -> IO ([Expr], MemoTable)
runSynth n (g, d) t st adtds = do
    (exps_deltas, (memot, _, _)) <- runReaderT (runStateT (observeManyT n $ synthComplete (g, d, []) t) st) $ initSynthReaderState (case recf of {[] -> ""; ((n, _):_) -> n}) adtds
    return (map fst exps_deltas, memot)

    where
        synthComplete (g, d, o) t = do
            (e, d') <- memoizesynth synth (recf, d, o) t <|> memoizesynth synth (g, d, o) t -- first try synth only with the recursive function in the gamma context instead of the whole program
            guard $ null d'
            return (e, d')

        recf = case g of
                 [] -> []
                 x:xs -> [x] -- head of Gamma is the recursive name since the recursive signature is the last added to the gamma context


initSynthState :: MemoTable -> Int -> SynthState
initSynthState mt i = (mt, Map.empty, i)


initSynthReaderState :: Name -> [ADTD] -> SynthReaderState
initSynthReaderState n a = ([], a, 0, [], n)





-------------------------------------------------------------------------------
-- Functions
-------------------------------------------------------------------------------

memoize :: Maybe (Maybe (Either (String, Scheme) (String, Type))) -> Ctxt -> Type -> Synth (Expr, Delta) -> Synth (Expr, Delta)
memoize maybefocus c t syn = do -- TODO: Can possibly be improved/optimized if we look at the existential type vars and restrictions... perhaps the hash function can play a role in it...
    (memot, cs, i) <- lift get
    res <- getres
    let key = hash c + hash (Map.toList cs) + hash res + hash t + hash maybefocus
    case Map.lookup key memot of
       Nothing -> do        -- If this synth hasn't been previously done -- run it and save the resulting values and state
           ifte syn
             (\(e, d') -> do
                 lift $ modify $ \(memot', cs', i') -> (Map.insert key (Just (e, d', cs', i'-i)) memot', cs', i')
                 return (e, d'))
             (do lift $ put (Map.insert key Nothing memot, cs, i)
                 empty)
       Just Nothing -> -- trace ("Speed up by skipping synth of " ++ show t)
           empty
       Just (Just (e, d', cs', deltai)) -> do 
           -- trace ("Speed up by skipping synth of " ++ show t ++ " and returning " ++ show e) $
           lift $ put (memot, cs', i + deltai)
           return (e, d') -- TODO: I think this has some issues with variable names that might collide

memoizesynth :: (Ctxt -> Type -> Synth (Expr, Delta)) -> Ctxt -> Type -> Synth (Expr, Delta)
memoizesynth syn c ty = memoize Nothing c ty (syn c ty)

memoizefocus :: (FocusCtxt -> Type -> Synth (Expr, Delta)) -> FocusCtxt -> Type -> Synth (Expr, Delta)
memoizefocus synf c@(g, d) ty = memoize Nothing (g, d, []) ty (synf c ty)

memoizefocus' :: (Maybe (String, Type) -> FocusCtxt -> Type -> Synth (Expr, Delta)) -> Maybe (String, Type) -> FocusCtxt -> Type -> Synth (Expr, Delta)
memoizefocus' syn fty c@(g, d) ty = memoize (Just (Right <$> fty)) (g, d, []) ty (syn fty c ty)

memoizefocusSch :: ((String, Scheme) -> FocusCtxt -> Type -> Synth (Expr, Delta)) -> (String, Scheme) -> FocusCtxt -> Type -> Synth (Expr, Delta)
memoizefocusSch syn fty c@(g, d) ty = memoize (Just (Just (Left fty))) (g, d, []) ty (syn fty c ty)


addconstraint :: Constraint -> Synth ()
addconstraint c = do
    (m, subs, i) <- lift get
    let maybesubs = solveconstraintsExistential subs c
    guard $ isJust maybesubs
    lift $ put (m, fromJust maybesubs, i)


addrestriction :: RestrictTag -> Type -> Synth a -> Synth a
addrestriction tag ty = local (\ (rs, adtds, d, t, e) -> ((tag, Right ty):rs, adtds, d, t, e))


addbinaryrestriction :: RestrictTag -> Type -> Type -> Synth a -> Synth a
addbinaryrestriction tag ty ty' = local (\ (rs, adtds, d, t, e) -> ((tag, Left (ty, ty')):rs, adtds, d, t, e))


addtrace :: TraceTag -> Synth a -> Synth a
addtrace t s = do
    (tstck, depth) <- gettracestack
    -- trace ("D" ++ show depth ++ ": " ++ show t ++ "\n-- stack --\n" ++ unlines (map show tstck) ++ "\n") $
    local (\(a,b,c,d,e) -> (a,b,c+1,t:d,e)) s


gettracestack :: Synth ([TraceTag], Int)
gettracestack = lift (lift ask) >>= \(a,b,c,d,e) -> return (d,c)


getdepth :: Synth Int
getdepth = lift (lift ask) >>= \(a,b,c,d,e) -> return c


checkrestrictions :: RestrictTag -> Type -> Synth Bool
checkrestrictions tag ty@(ADT tyn tpl) = do -- Restrictions only on ADT Construction and Destruction
    rs <- lift (lift ask) >>= \(a,b,c,d,e) -> return a
    subs <- getsubs
    let reslist = rights $ map snd $ filter (\(n,x) -> n == tag) rs
    let b = ty `notElem` reslist && not (any isExistentialType $ filter (\(ADT tyn' _) -> tyn == tyn') reslist)
    -- trace ("Is " ++ show ty ++ " (" ++ show (apply subs ty) ++ ") restricted by any of " ++ show reslist ++ " ? -> " ++ show (not b)) $
    return b

checkrestrictions' :: Restrictions -> RestrictTag -> Type -> Synth Bool
checkrestrictions' rs tag ty@(ADT tyn tpl) = do -- Restrictions only on ADT Construction and Destruction
    let reslist = rights $ map snd $ filter (\(n,x) -> n == tag) rs
    return $ ty `notElem` reslist && not (any isExistentialType $ filter (\(ADT tyn' _) -> tyn == tyn') reslist)


getres :: Synth Restrictions
getres = lift (lift ask) >>= \(a,b,c,d,e) -> return a


checkbinaryrestrictions :: RestrictTag -> (Type, Type) -> Synth Bool
checkbinaryrestrictions tag typair = do
    rs <- lift (lift ask) >>= \(a,b,c,d,e) -> return a
    subs <- getsubs
    let reslist = lefts $ map snd $ filter (\(n,x) -> n == tag) rs
    let b = typair `notElem` reslist && all ((not . isExistentialType) . snd) reslist
    -- trace ("Is " ++ show typair  ++ " (" ++ show (apply subs typair) ++ ") restricted by any of " ++ show reslist ++ " ? -> " ++ show (not b)) $
    return b


getadtcons :: Type -> Synth [(Name, Type)] -- Handles substitution of polimorfic types with actual type in constructors
getadtcons (ADT tyn tps) = do
    adtds <- lift (lift ask) >>= \(a,b,c,d,e) -> return b
    case find (\(ADTD name ps _) -> tyn == name && length tps == length ps) adtds of
      Just (ADTD _ paramvars cons) ->
          let subst = Map.fromList $ zip paramvars tps in
          return $ map (apply subst) cons
      Nothing -> return []


getsubs :: Synth Subst
getsubs = (\(a,b,c) -> b) <$> lift get


clearsubs :: Synth ()
clearsubs = modify (\(m, s, i) -> (m, Map.empty, i))


removerecself :: Gamma -> Synth Gamma
removerecself g = do
    recself <- getrecself
    return $ deleteBy (\ a b -> fst a == fst b) (recself, undefined) g
        where
            getrecself :: Synth Name
            getrecself = lift (lift ask) >>= \(a,b,c,d,e) -> return e


fresh :: Synth String
fresh = do 
    (m, cs, n) <- lift get
    lift $ put (m, cs, n+1)
    return $ getName n


freshIndex :: Synth Int
freshIndex = do 
    (m, cs, n) <- lift get
    lift $ put (m, cs, n+1)
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
       ExistentialTypeVar _ -> True
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
        ftvctx' acc (gc, dc) = Set.unions (map (ftvctx'' . snd) gc) `Set.union` Set.unions (map (ftv . snd) dc)
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

synth :: Ctxt -> Type -> Synth (Expr, Delta)

---- * Right asynchronous rules * -----------------

---- -oR
synth c@(г, d, o) (Fun a b) = addtrace (RightFun c (Fun a b)) $ do
    name <- fresh
    (exp, d') <- memoizesynth synth (г, d, (name, a):o) b
    guard (name `notElem` map fst d')
    return (Abs name (Just a) exp, d')

---- &R
synth c (With a b) = addtrace (RightWith c (With a b)) $ do
    (expa, d') <- memoizesynth synth c a
    (expb, d'') <- memoizesynth synth c b
    guard (d' == d'')
    return (WithValue expa expb, d')

-- no more synchronous right propositions, start inverting the ordered context (Ω)



---- * Left asynchronous rules * ------------------

---- *L
synth c@(g, d, (n, Tensor a b):o) t = addtrace (LeftTensor c (Tensor a b) t) $ do
    n1 <- fresh
    n2 <- fresh
    (expt, d') <- memoizesynth synth (g, d, (n2, b):(n1, a):o) t
    guard ((n1 `notElem` map fst d') && (n2 `notElem` map fst d'))
    return (LetTensor n1 n2 (Var n) expt, d')

---- 1L
synth c@(g, d, (n, Unit):o) t = addtrace (LeftUnit c t) $ do
    (expt, d') <- memoizesynth synth (g, d, o) t
    return (LetUnit (Var n) expt, d')

---- +L
synth c@(g, d, (n, Plus a b):o) t = addtrace (LeftPlus c (Plus a b) t) $ do
    n1 <- fresh
    n2 <- fresh
    (expa, d') <- memoizesynth synth (g, d, (n1, a):o) t
    (expb, d'')  <- memoizesynth synth (g, d, (n2, b):o) t
    guard (d' == d'')
    guard ((n1 `notElem` map fst d') && (n2 `notElem` map fst d'))
    return (CaseOfPlus (Var n) n1 expa n2 expb, d')

---- sumL
synth (g, d, (n, Sum tys):o) t = addtrace (LeftSum (Sum tys) t) $ do
    ls <- mapM (\(name, ct) -> do
        varid <- fresh
        (exp, d') <- memoizesynth synth (g, d, (varid, ct):o) t
        guard $ varid `notElem` map fst d'
        return (name, varid, exp, d')
        ) tys
    let (n1, varid1, e1, d1') = head ls
    guard $ all ((== d1') . (\(_,_,_,c) -> c)) (tail ls)
    return (CaseOfSum (Var n) (map (\(n,i,e,_) -> (n,i,e)) ls), d1')

---- adtL
synth c@(g, d, p@(n, ADT tyn tps):o) t = (lift (lift ask) >>= \(res,_,_,_,_) -> addtrace (LeftADT res c (ADT tyn tps) t) $ do
    checkrestrictions DeconstructADT (ADT tyn tps) >>= guard
    adtds <- getadtcons (ADT tyn tps)
    if null adtds
       then addrestriction DeconstructADT (ADT tyn tps) $ memoizesynth synth (g, p:d, o) t    -- An ADT that has no constructors might still be used to instantiate a proposition, but shouldn't leave synchronous mode (hence the restriction)
       else do
            isrectype <- isRecursiveType (ADT tyn tps)
            ls <- mapM (\(name, vtype) ->
                (if isrectype -- TODO: make restrictions not dependent
                   then addrestriction DeconstructADT (ADT tyn tps)           -- For recursive types, restrict deconstruction of this type in further computations
                   else id) $
                   (if t /= ADT tyn tps
                       then addrestriction ConstructADT (ADT tyn tps)         -- If the goal is anything but the recursive type, restrict construction of type to avoid "stupid functions"
                       else id) $
                        case vtype of
                          Unit -> do
                            g' <- removerecself g -- !TODO: Verificar correto: Eliminar do branch sem elementos a chamada recursiva
                            (exp, d') <- memoizesynth synth (g', d, o) t
                            return (name, "", exp, d')
                          argty -> do
                            varid <- fresh
                            (exp, d') <- memoizesynth synth (g, d, (varid, argty):o) t
                            guard $ varid `notElem` map fst d'
                            return (name, varid, exp, d')
                  -- TODO: polymorphic ADT
                ) adtds
            let (n1, varid1, e1, d1') = head ls
            guard $ all ((== d1') . (\(_,_,_,c) -> c)) (tail ls) -- all resulting contexts are the same
            return (CaseOf (Var n) (map (\(n, vari, exp, _) -> (n, vari, exp)) ls), d1')
    ) <|> (
    lift (lift ask) >>= \(res,_,_,_,_) -> addtrace (MoveLeftADT res c (ADT tyn tps) t) $ do
    checkrestrictions DeconstructADT (ADT tyn tps) >>= guard . not          -- ADT with a restriction on deconstruction might still be useful by being instantiated while focused -- e.g. a Tensor was deconstructed asynchronously but the ADT has a deconstruct restriction -- it shouldn't fail, yet it shouldn't deconstruct either -- this option covers that case (Similar to "Move To Delta" but for ADTs that we cannot deconstruct any further)
    memoizesynth synth (g, p:d, o) t)                                                    -- So if we failed above because a restriction didn't allow us to invert this ADT, try using the hypothesis in the linear context -- it won't loop back here because the DeconstructADT

---- !L
synth c@(g, d, (n, Bang a):o) t = addtrace (LeftBang c (Bang a) t) $ do
    nname <- fresh
    (exp, d') <- memoizesynth synth ((nname, Right a):g, d, o) t
    guard (nname `notElem` map fst d')
    return (LetBang nname (Var n) exp, d')

---- refinementL
synth c@(g, d, rn@(n, r@RefinementType {}):o) t = addtrace (LeftRefinement c rn t) $ do
    let t' = addRefinementToCtxs r t    -- Add this refinement to the context of refinement types in t
    synth (g, rn:d, o) t'


---- * Synchronous left propositions to Δ * -------

synth (g, d, p:o) t =
    addtrace (MoveToDelta p t) $ memoizesynth synth (g, p:d, o) t



---- * Synchronous rules * -------------------------

-- no more asynchronous propositions, focus

synth c@(g, d, []) t = lift (lift ask) >>= \(res,_,_,_,_) -> addtrace (Focus res c t) $
    memoizefocus focus (g, d) t


focus :: FocusCtxt -> Type -> Synth (Expr, Delta)
focus c goal =
    decideLeft c goal <|> decideRight c goal <|> decideLeftBang c goal -- deciding left before right will be correct more often than not (at least based on recent attempts...) -- !TODO: Deciding Right before Left can lead to infinite loops!! (Ex: Expr = Var Nat | Lam Expr)

    where
        decideRight, decideLeft, decideLeftBang :: FocusCtxt -> Type -> Synth (Expr, Delta)

        decideRight c goal = addtrace (DecideRight goal) $
            if isAtomic goal                            -- to decide right, goal cannot be atomic
                then empty
                else do
                    assertADTHasCons goal >>= guard     -- to decide right, goal cannot be an ADT that has no constructors
                    memoizefocus' focus' Nothing c goal


        decideLeft (g, din) goal =
            case din of
              []     -> empty
              _ -> foldr ((<|>) . (\nx@(n,x) -> addtrace (DecideLeft x goal) $ memoizefocus' focus' (Just nx) (g, delete nx din) goal)) empty din


        decideLeftBang (g, din) goal =
            case g of
              []   -> empty
              _ -> do
                  (res, _, _, _, _) <- lift $ lift ask
                  foldr ((<|>) . (\case
                                    (n, Right x) -> addtrace (DecideLeftBang res x goal) $
                                        managerestrictions x $
                                            memoizefocus' focus' (Just (n, x)) (g, din) goal;
                                    (n, Left sch) -> addtrace (DecideLeftBangSch res sch goal) $
                                        managerestrictions (instantiateFrom 0 sch) $
                                            memoizefocusSch focusSch (n, sch) (g, din) goal)) empty g
                                 where
                                     managerestrictions :: Type -> Synth a -> Synth a
                                     managerestrictions x s = do    -- Restrict re-usage of decide left bang to synth the same time a second time
                                         checkbinaryrestrictions DecideLeftBangR (x, goal) >>= guard
                                         addbinaryrestriction DecideLeftBangR x goal s

        
            
        ---- Eliminating Schemes
        focusSch :: (String, Scheme) -> FocusCtxt -> Type -> Synth (Expr, Delta)

        ---- VL
        focusSch (n, sch@(Forall ns t)) ctxt goal = do
            (et, etvars) <- existencialInstantiate sch                                          -- tipo com existenciais
            addtrace (FocusLeftScheme (n, et) ctxt goal) $ do
                -- can only try scheme if current constraints are still safe
                -- before trying to synth Unit to use as the instanciation of an existential ?x, make sure this new constraint doesn't violate previous constraints,
                -- or else we might try to synth Unit assuming ?x again, which will fail solving the constraints, which in turn will make the Unit try to be synthed again using the other choice which is to assume ?x again...
                -- TODO: Verify and explain resoning to make sure it's correct (e.g. let id = (\x -o x); let main = {{ ... }} loops infintely without this)
                -- (et, etvars) <- existencialInstantiate sch                                          -- tipo com existenciais
                (se, d') <- memoizefocus' focus' (Just (n, et)) ctxt goal                                         -- fail ou success c restrições -- sempre que é adicionada uma constraint é feita a unificação
                unifysubs <- getsubs
                                                                                                    -- resolve ou falha -- por conflito ou falta informação
                                                                                                    -- por conflicto durante o processo
                guard (Set.disjoint (Set.fromList etvars) (ftv $ apply unifysubs et))               -- por falta de informação (não pode haver variáveis existenciais bound que fiquem por instanciar, i.e. não pode haver bound vars nas ftvs do tipo substituido)
                clearsubs                                                                           -- after making sure no instantiated variables escaped, clear the current substitution so that it doesn't complicate further scheme computations
                return (se, d')                                                                     -- if constraints are "total" and satisfiable, the synth using a polymorphic type was successful
                    where
                        existencialInstantiate (Forall ns t) = do
                            netvs <- mapM (const $ do {i <- freshIndex; return (ExistentialTypeVar i, -i)}) ns
                            return (apply (Map.fromList $ zip ns $ map fst netvs) t, map snd netvs)



        focus' :: Maybe (String, Type) -> FocusCtxt -> Type -> Synth (Expr, Delta)

        ---- * Right synchronous rules * ------------------

        ---- *R
        focus' Nothing c@(g, d) (Tensor a b) = addtrace (RightTensor c (Tensor a b)) $ do
            (expa, d') <- case a of { ADT _ _ -> memoizefocus focus c a; _ -> memoizefocus' focus' Nothing c a }
            (expb, d'') <- case b of { ADT _ _ -> memoizefocus focus (g, d') b; _ -> memoizefocus' focus' Nothing (g, d') b }
            return (TensorValue expa expb, d'')

        ---- 1R
        focus' Nothing c@(g, d) Unit = addtrace (RightUnit c) $
            return (UnitValue, d)
            
        ---- +R
        focus' Nothing c (Plus a b) = addtrace (RightPlus c (Plus a b)) $ do
            (il, d') <- case a of { ADT _ _ -> memoizefocus focus c a; _ -> memoizefocus' focus' Nothing c a }
            return (InjL (Just b) il, d')
            `interleave` do
            (ir, d') <- case b of { ADT _ _ -> memoizefocus focus c b; _ -> memoizefocus' focus' Nothing c b }
            return (InjR (Just a) ir, d')

        ---- sumR
        focus' Nothing c (Sum sts) = addtrace (RightSum (Sum sts)) $
            foldr (interleave . (\(tag, goalt) ->
                do
                   (e, d') <- case goalt of { ADT _ _ -> memoizefocus focus c goalt; _ -> memoizefocus' focus' Nothing c goalt }
                   let smts = map (second Just) $ delete (tag, goalt) sts
                   return (SumValue smts (tag, e), d')
                )) empty sts

        ---- adtR
        focus' Nothing c@(g, d) (ADT tyn pts) = lift (lift ask) >>= \(res,_,_,_,_) -> do
            cons <- getadtcons (ADT tyn pts)
            foldr (interleave . (\(tag, argty) ->
                addtrace (RightADT tag res c (ADT tyn pts)) $
                   case argty of
                     Unit -> return (Var tag, d)        -- The branch where this constructor is used might fail later e.g. if an hypothesis isn't consumed from delta when it should have
                     argtype -> do
                         -- rs <- lift (lift ask) >>= \(a,b,c,d,e) -> return a
                         -- let reslist = rights $ map snd $ filter (\(n,x) -> n == ConstructADT) rs
                         checkrestrictions' res ConstructADT (ADT tyn pts) >>= guard
                         -- trace ("Check if " ++ show (ADT tyn pts) ++ " is not restricted by " ++ show reslist ++ " in " ++ show rs ++ " : " ++ show b ++ "? ?? " ++ show res) $ checkrestrictions' res ConstructADT (ADT tyn pts) >>= guard     -- Assert this ADT's construction isn't restricted
                         if case argtype of
                                ADT tyn' pts' -> tyn == tyn' && pts == pts'         -- If the constructor for an ADT takes itself as a parameter, focus right should fail and instead focus left. -- TODO: Questionable
                                _ -> False
                            then empty
                            else addrestriction ConstructADT (ADT tyn pts) $ do     -- Cannot construct ADT t as means to construct ADT t -- might cause an infinite loop
                                (arge, d') <- case argtype of { ADT _ _ -> memoizefocus focus c argtype; _ -> memoizefocus' focus' Nothing c argtype }
                                return (App (Var tag) arge, d')
                )) empty cons
            -- When we're right focused, we might continue right focused as we construct the proof (e.g. RightTensor),
            -- However, where other propositions would loop back to asynch mode, and back again to the decision point,
            -- Allowing for a left decision and an eventual instantiation of the goal,
            -- A restricted ADT might fail right away while being right focused, and never considered the possibility of deciding left to instantiate it
            -- Knowning so, all `focus right` expressions will instead just `focus` (and `decide`) on algebraic data types (ADT)s
           

        ---- !R
        focus' Nothing c@(g, d) (Bang a) = addtrace (RightBang c (Bang a)) $ do
            (expa, d') <- memoizesynth synth (g, d, []) a
            guard (d == d')
            return (BangValue expa, d')


        ---- refinementR
        focus' Nothing c@(g, d) r@(RefinementType rname ty rctx mpred) = addtrace (RightRefinement c r) $
            case mpred of
              Nothing -> focus' Nothing c ty    -- If there's no predicate try instancing the type
              Just pred -> do
                  model <- liftIO $ getModelExpr r
                  case model of
                    Nothing -> empty   -- the SMT solver couldn't generate a model for this predicate
                    Just expr -> error ("Got model " ++ show expr ++ " and now utilizing variables to instance it")


        ---- * Left synchronous rules * -------------------

        ---- -oL
        focus' (Just (n, Fun a b)) c@(g, d) goal = addtrace (LeftFun c (Fun a b) goal) $ do
            nname <- fresh
            (expb, d') <- memoizefocus' focus' (Just (nname, b)) c goal
            guard (nname `notElem` map fst d')
            -- subs <- getsubs
            -- (expa, d'') <- synth (g, apply subs d', []) (apply subs a) -- TODO?
            (expa, d'') <- memoizesynth synth (g, d', []) a
            return (substitute nname (App (Var n) expa) expb, d'')
            
        ---- &L
        focus' (Just (n, With a b)) c goal = addtrace (LeftWith c (With a b) goal) $
            do
                nname <- fresh
                (lf, d') <- memoizefocus' focus' (Just (nname, a)) c goal
                guard (nname `notElem` map fst d')
                return (substitute nname (Fst (Var n)) lf, d')
            <|>
            do
                nname <- fresh
                (rt, d') <- memoizefocus' focus' (Just (nname, b)) c goal
                guard (nname `notElem` map fst d')
                return (substitute nname (Snd (Var n)) rt, d')

        ---- ∃L (?)
        focus' (Just (n, ExistentialTypeVar x)) (g, d) goal = addtrace LeftExistentialTV $
            case goal of
              (ExistentialTypeVar y) ->
                  if x == y then return (Var n, d)          -- ?a |- ?a succeeds
                            else empty                      -- ?a |- ?b fails
              _ -> do                                       -- ?a |- t  succeeds with constraint
                  addconstraint $ Constraint (ExistentialTypeVar x) goal
                  return (Var n, d)



        ---- * Proposition no longer synchronous * --------

        ---- adtLFocus
        ---- if we're focusing left on an ADT X while trying to synth ADT X, instead of decomposing the ADT as we do when inverting rules, we'll instance the var right away -- to tame recursive types
        focus' (Just nh@(n, ADT tyn tps)) c@(g, d) goal = addtrace (FocusLeftADT c (ADT tyn tps) goal) $
            if case goal of
                 ADT tyn' tps' -> tyn' == tyn
                 _ -> False
              then do
                  let (ADT tyn' tps') = goal
                  zipWithM_ unifyadtparams tps tps'
                  return (Var n, d)
              else do
                  adtcns <- getadtcons (ADT tyn tps) 
                  guard $ not $ null adtcns                                 -- If the type can't be desconstructed fail here, trying it asynchronously will force another focus/decision of goal -- which under certain circumstances causes an infinite loop
                  checkrestrictions DeconstructADT (ADT tyn tps) >>= guard  -- Assert ADT to move to omega can be deconstructed. ADTs that can't would loop back here if they were to be placed in omega
                  memoizesynth synth (g, d, [nh]) goal
                      where
                          unifyadtparams :: Type -> Type -> Synth ()
                          unifyadtparams (ADT tyn'' tps'') (ADT tyn''' tps''') = do
                              guard $ tyn'' == tyn'''
                              zipWithM_ unifyadtparams tps'' tps'''
                          unifyadtparams (ExistentialTypeVar x) y = addconstraint $ Constraint (ExistentialTypeVar x) y
                          unifyadtparams x (ExistentialTypeVar y) = unifyadtparams (ExistentialTypeVar y) x
                          unifyadtparams x y = guard (x == y)


        ---- refinementLFocus
        focus' (Just nh@(n, RefinementType rname ty rctx mpred)) c@(g, d) goal = addtrace (FocusLeftRefinement c nh goal) $
            case goal of
              RefinementType {} -> empty    -- using proposition to instance a refinement type requires extra logic
              _ -> focus' (Just (n, ty)) c goal -- using the focus proposition to instance any other type is the same as using the type without the refinements


        ---- left focus is either atomic or not.
        ---- if it is atomic, it'll either be the goal and instanciate it, or fail
        ---- if it's not atomic, and it's not left synchronous, unfocus

        focus' (Just nh@(n, h)) c@(g, d) goal
          | isAtomic h                      -- left focus is atomic
          = addtrace (DefaultFocusLeft c nh goal) $
          do case goal of
                 (ExistentialTypeVar x)     -- goal is an existential proposition generate a constraint and succeed -- TODO: Fiz isto em vez de ter uma regra para left focus on TypeVar para Existencial porque parece-me que Bool |- ?a tmb deve gerar um constraint ?a => Bool, certo?
                   -> do
                        addconstraint $ Constraint (ExistentialTypeVar x) h
                        return (Var n, d)
                 _ -> do
                        guard (h == goal)  -- if is atomic and not the goal, fail
                        return (Var n, d)  -- else, instantiate it
          | otherwise
          = addtrace (DefaultFocusLeft c nh goal) $ memoizesynth synth (g, d, [nh]) goal         -- left focus is not atomic and not left synchronous, unfocus



        ---- right focus is not synchronous, unfocus.

        focus' Nothing c (ExistentialTypeVar _) = empty

        focus' Nothing c@(g, d) goal = addtrace (DefaultFocusRight c goal) $
            memoizesynth synth (g, d, []) goal -- <|> if t refined then smt solve t with join context refined with && else empty





-------------------------------------------------------------------------------
-- Functions
-------------------------------------------------------------------------------

removeadtcons :: [ADTD] -> (Gamma, Delta) -> (Gamma, Delta)
removeadtcons adts (fc, bc) = case adts of -- During the synth process, constructors should only be used when focused right on the ADT -- so remove them from the unrestricted context
    [] -> (fc, bc)
    (ADTD _ _ cons):xs -> removeadtcons xs (filter (\(n, _) -> isNothing $ lookup n cons) fc, bc)


synthCtxAllType :: Int -> MemoTable -> (Gamma, Delta) -> Int -> [ADTD] -> Type -> IO ([Expr], MemoTable)
synthCtxAllType n mt c i adts t = do
    let c' = removeadtcons adts c
    (exps, memot) <- runSynth n c' t (initSynthState mt i) adts
    if null exps
        then error $ "[Synth] Failed synthesis of: " ++ show t
        else return (exps, memot)


synthCtxType :: MemoTable -> (Gamma, Delta) -> Int -> [ADTD] -> Type -> IO (Expr, MemoTable)
synthCtxType mt c i adts t = do
    (exps, memot) <- synthCtxAllType 1 mt c i adts t
    return (head exps, memot)




-------------------------------------------------------------------------------
-- Exported Functions
-------------------------------------------------------------------------------

synthAllType :: Type -> IO [Expr]
synthAllType t = fst <$> synthCtxAllType 5 Map.empty ([], []) 0 [] t -- Not really *all* bc runSynth might loop forever?


synthType :: Type -> IO Expr
synthType t = head <$> synthAllType (instantiateFrom 0 $ generalize ([], []) t)


synthMarks :: Expr -> [ADTD] -> (StateT MemoTable IO) Expr -- replace all placeholders in an expression with a synthetized expr
synthMarks ex adts = transformM transformfunc ex
    where
        transformfunc :: Expr -> (StateT MemoTable IO) Expr
        transformfunc =
            \case
                (Mark _ name c@(fc, bc) t) -> do
                    mt <- get
                    let sch@(Forall tvs t') = fromMaybe (error "[Synth] Failed: Marks can't be synthetized without a type.") t
                    case name of
                      Nothing    -> do -- Non-recursive Mark
                        (exp, memot') <- liftIO $ synthCtxType mt c (length tvs) adts $ instantiateFrom 0 sch
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
                                              (exp, memot') <- liftIO $ synthCtxType mt c i adts t2
                                              modify (`Map.union` memot')
                                              return (name, "", exp)
                                          argty -> do
                                              (exp, memot') <- liftIO $ synthCtxType mt ((name', Left sch):fc, (getName i, argty):(name', instantiateFrom 0 sch):bc) (i+1) adts t2
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


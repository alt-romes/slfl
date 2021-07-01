{-# LANGUAGE LambdaCase #-}
module Synth (synthAllType, synthType, synthMarks, synthMarksModule) where

import Data.List
import qualified Data.Set as Set
import qualified Data.Map as Map
import Control.Applicative
import Control.Monad.Logic
import Control.Monad.State
import Control.Monad.Reader
import Data.Maybe
import Data.Bifunctor
import Debug.Trace


import CoreSyntax (Name, Type(..), Scheme(..), isInType)
import Syntax
import Program
import Util
import Constraints
import Typechecker (instantiateFrom)



type Gamma = [(Name, Either Scheme Type)] -- Unrestricted hypothesis              (Γ)
type Delta = [(Name, Type)]       -- Linear hypothesis (not left asynchronous)    (Δ)
type Omega = [(Name, Type)]       -- Ordered (linear?) hypothesis                 (Ω)
type Ctxt = (Gamma, Delta, Omega)   -- Delta out is a return value
type FocusCtxt = (Gamma, Delta)     -- Gamma, DeltaIn

-------------------------------------------------------------------------------
-- Synth "Monad"
-------------------------------------------------------------------------------

type Synth a = LogicT (StateT SynthState (Reader SynthReaderState)) a 


type SynthState = ([Constraint], Int)  -- (list of constraints added by the process to solve when instantiating a scheme, next index to instance a variable)


type SynthReaderState = (Restrictions, [ADTD], Int, [TraceTag]) -- (list of restrictions applied on types in specific places, list of ADTDs to be always present)
type Restriction = Type -> Bool
type Restrictions = [(RestrictTag, Restriction)]


data RestrictTag = ConstructADT | DeconstructADT | DecideLeftBangR deriving (Eq)

data TraceTag = RightFun Ctxt Type | RightWith Ctxt Type | LeftTensor Ctxt Type Type | LeftUnit Ctxt Type | LeftPlus Ctxt Type Type | LeftSum Type Type | LeftADT Ctxt Type Type | LeftBang Ctxt Type Type | MoveToDelta (Name, Type) Type | Focus Ctxt Type | DecideLeft Type Type | DecideRight Type | DecideLeftBang Type Type | DecideLeftBangSch Scheme Type | FocusLeftScheme | RightTensor FocusCtxt Type | RightUnit FocusCtxt | RightPlus FocusCtxt Type | RightSum Type | RightADT FocusCtxt Type | RightBang FocusCtxt Type | LeftFun FocusCtxt Type Type | LeftWith FocusCtxt Type Type | LeftExistentialTV | FocusLeftADT FocusCtxt Type Type | DefaultFocusLeft FocusCtxt (Name, Type) Type | DefaultFocusRight FocusCtxt Type deriving (Show)


runSynth :: (Gamma, Delta) -> Type -> SynthState -> [ADTD] -> [(Expr, Delta)]
runSynth (g, d) t st adtds = runReader (evalStateT (observeAllT $ synthComplete (g, d, []) t) st) $ initSynthReaderState adtds
    where
        synthComplete (g, d, o) t = do
            (e, d') <- synth (g, d, o) t
            guard $ null d'
            return (e, d')


initSynthState :: Int -> SynthState
initSynthState i = ([], i)


initSynthReaderState :: [ADTD] -> SynthReaderState
initSynthReaderState a = ([], a, 0, [])





-------------------------------------------------------------------------------
-- Functions
-------------------------------------------------------------------------------

addconstraint :: Constraint -> Synth ()
addconstraint c = lift $ modify (first (c :))


addrestriction :: RestrictTag -> Type -> Synth a -> Synth a
addrestriction tag ty = local (\ (rs, adtds, d, t) -> ((tag, (/= ty)):rs, adtds, d, t))


addtrace :: TraceTag -> Synth a -> Synth a
addtrace t s = do
    (tstck, depth) <- gettracestack
    trace ("D" ++ show depth ++ ": " ++ show t ++ "\n-- stack --\n" ++ unlines (map show tstck) ++ "\n") $
        local (\(a,b,c,d) -> (a,b,c+1,t:d)) s


gettracestack :: Synth ([TraceTag], Int)
gettracestack = lift (lift ask) >>= \(a,b,c,d) -> return (d,c)


getdepth :: Synth Int
getdepth = lift (lift ask) >>= \(a,b,c,d) -> return c


getrestrictions :: RestrictTag -> Synth [Restriction]
getrestrictions tag = do
    rs <- lift (lift ask) >>= \(a,b,c,d) -> return a
    return $ map snd $ filter (\(n,_) -> n == tag) rs


getadtcons :: Type -> Synth [(Name, Type)] -- Handles substitution of polimorfic types with actual type in constructors
getadtcons (ADT tyn tps) = do
    adtds <- lift (lift ask) >>= \(a,b,c,d) -> return b
    case find (\(ADTD name ps _) -> tyn == name && length tps == length ps) adtds of
      Just (ADTD _ paramvars cons) ->
          let subst = Map.fromList $ zip paramvars tps in
          return $ map (apply subst) cons
      Nothing -> return []


clearrestrictions :: RestrictTag -> Synth a -> Synth a
clearrestrictions tag = local (\(rs,b,c,d) -> (filter (\(n,_) -> n /= tag) rs, b, c, d))


fresh :: Synth String
fresh = do 
    (cs, n) <- lift get
    lift $ put (cs, n+1)
    return $ getName n


freshIndex :: Synth Int
freshIndex = do 
    (cs, n) <- lift get
    lift $ put (cs, n+1)
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
    (exp, d') <- synth (г, d, (name, a):o) b
    guard (name `notElem` map fst d')
    return (Abs name (Just a) exp, d')

---- &R
synth c (With a b) = addtrace (RightWith c (With a b)) $ do
    (expa, d') <- synth c a
    (expb, d'') <- synth c b
    guard (d' == d'')
    return (WithValue expa expb, d')

-- no more synchronous right propositions, start inverting the ordered context (Ω)



---- * Left asynchronous rules * ------------------

---- *L
synth c@(g, d, (n, Tensor a b):o) t = addtrace (LeftTensor c (Tensor a b) t) $ do
    n1 <- fresh
    n2 <- fresh
    (expt, d') <- synth (g, d, (n2, b):(n1, a):o) t
    guard ((n1 `notElem` map fst d') && (n2 `notElem` map fst d'))
    return (LetTensor n1 n2 (Var n) expt, d')

---- 1L
synth c@(g, d, (n, Unit):o) t = addtrace (LeftUnit c t) $ do
    (expt, d') <- synth (g, d, o) t
    return (LetUnit (Var n) expt, d')

---- +L
synth c@(g, d, (n, Plus a b):o) t = addtrace (LeftPlus c (Plus a b) t) $ do
    n1 <- fresh
    n2 <- fresh
    (expa, d') <- synth (g, d, (n1, a):o) t
    (expb, d'')  <- synth (g, d, (n2, b):o) t
    guard (d' == d'')
    guard ((n1 `notElem` map fst d') && (n2 `notElem` map fst d'))
    return (CaseOfPlus (Var n) n1 expa n2 expb, d')

---- sumL
synth (g, d, (n, Sum tys):o) t = addtrace (LeftSum (Sum tys) t) $ do
    ls <- mapM (\(name, ct) -> do
        varid <- fresh
        (exp, d') <- synth (g, d, (varid, ct):o) t
        guard $ varid `notElem` map fst d'
        return (name, varid, exp, d')
        ) tys
    let (n1, varid1, e1, d1') = head ls
    guard $ all ((== d1') . (\(_,_,_,c) -> c)) (tail ls)
    return (CaseOfSum (Var n) (map (\(n,i,e,_) -> (n,i,e)) ls), d1')

---- adtL
synth c@(g, d, p@(n, ADT tyn tps):o) t = addtrace (LeftADT c (ADT tyn tps) t) (do
    res <- getrestrictions DeconstructADT
    guard $ all (\f -> f (ADT tyn tps)) res -- Assert destruction of this type isn't restricted
    adtds <- getadtcons (ADT tyn tps)
    if null adtds
       then addrestriction DeconstructADT (ADT tyn tps) $ synth (g, p:d, o) t    -- An ADT that has no constructors might still be used to instantiate a proposition, but shouldn't leave synchronous mode (hence the restriction)
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
                            (exp, d') <- synth (g, d, o) t
                            return (name, "", exp, d')
                          argty -> do
                            varid <- fresh
                            (exp, d') <- synth (g, d, (varid, argty):o) t
                            guard $ varid `notElem` map fst d'
                            return (name, varid, exp, d')
                  -- TODO: polymorphic ADT
                ) adtds
            let (n1, varid1, e1, d1') = head ls
            guard $ all ((== d1') . (\(_,_,_,c) -> c)) (tail ls) -- all resulting contexts are the same
            return (CaseOf (Var n) (map (\(n, vari, exp, _) -> (n, vari, exp)) ls), d1')
    <|>
    do
    res <- getrestrictions DeconstructADT                       -- ADT with a restriction on deconstruction might still be useful by being instantiated while focused -- e.g. a Tensor was deconstructed asynchronously but the ADT has a deconstruct restriction -- it shouldn't fail, yet it shouldn't deconstruct either -- this option covers that case (Similar to "Move To Delta" but for ADTs that we cannot deconstruct any further)
    guard $ not $ all (\f -> f (ADT tyn tps)) res                   -- So if we failed above because a restriction didn't allow us to invert this ADT
    synth (g, p:d, o) t)                                        -- Try using the hypothesis in the linear context -- it won't loop back here because the DeconstructADT

---- !L
synth c@(g, d, (n, Bang a):o) t = addtrace (LeftBang c (Bang a) t) $ do
    nname <- fresh
    (exp, d') <- synth ((nname, Right a):g, d, o) t
    guard (nname `notElem` map fst d')
    return (LetBang nname (Var n) exp, d')



---- * Synchronous left propositions to Δ * -------

synth (g, d, p:o) t =
    addtrace (MoveToDelta p t) $ synth (g, p:d, o) t



---- * Synchronous rules * -------------------------

-- no more asynchronous propositions, focus

synth c@(g, d, []) t = addtrace (Focus c t) $
    focus (g, d) t


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
                    focus' Nothing c goal


        decideLeft (g, din) goal =
            case din of
              []     -> empty
              _ -> foldr ((<|>) . (\nx@(n,x) -> addtrace (DecideLeft x goal) $ focus' (Just nx) (g, delete nx din) goal)) empty din


        decideLeftBang (g, din) goal =
            case g of
              []   -> empty
              _ -> foldr ((<|>) . (\case
                                    (n, Right x) -> addtrace (DecideLeftBang x goal) $
                                        managerestrictions x $
                                            focus' (Just (n, x)) (g, din) goal;
                                    (n, Left sch) -> addtrace (DecideLeftBangSch sch goal) $
                                        managerestrictions (instantiateFrom 0 sch) $ -- For perfect correctness it would probably be best to have restrictions just for the schemes, but this will work since this is the only point where a restriction on schemes is checked and set, meaning their "instances from 0" will all be the same
                                            focusSch (n, sch) (g, din) goal)) empty g
                                 where
                                     managerestrictions :: Type -> Synth a -> Synth a
                                     managerestrictions x s = do
                                        res <- getrestrictions DecideLeftBangR
                                        guard $ all (\f -> f x) res
                                        (if case x of
                                            Fun a b -> a == goal
                                            _ -> False
                                           then addrestriction DecideLeftBangR x
                                           else id) s

        
            
        ---- Eliminating Schemes
        focusSch :: (String, Scheme) -> FocusCtxt -> Type -> Synth (Expr, Delta)

        ---- VL
        focusSch (n, sch@(Forall ns t)) ctxt goal = addtrace FocusLeftScheme $ do
            -- can only try scheme if current constraints are still safe
            -- before trying to synth Unit to use as the instanciation of an existential ?x, make sure this new constraint doesn't violate previous constraints,
            -- or else we might try to synth Unit assuming ?x again, which will fail solving the constraints, which in turn will make the Unit try to be synthed again using the other choice which is to assume ?x again...
            -- TODO: Verify and explain resoning to make sure it's correct (e.g. let id = (\x -o x); let main = {{ ... }} loops infintely without this)
            (et, etvars) <- existencialInstantiate sch                                          -- tipo com existenciais
            (se, d') <- focus' (Just (n, et)) ctxt goal                                         -- fail ou success c restrições
            (constrs, _) <- lift get
            let unify = solveconstraintsExistential Map.empty constrs                           -- resolve ou falha -- por conflito ou falta informação
            guard (isJust unify)                                                                -- por conflicto
            guard (Set.disjoint (Set.fromList etvars) (ftv $ apply (fromJust unify) et))        -- por falta de informação (não pode haver variáveis existenciais bound que fiquem por instanciar, i.e. não pode haver bound vars nas ftvs do tipo substituido) -- TODO: Não produz coisas erradas mas podemos estar a esconder resultados válidos
            return (se, d')                                                                     -- if constraints are "total" and satisfiable, the synth using a polymorphic type was successful
                where
                    existencialInstantiate (Forall ns t) = do
                        netvs <- mapM (const $ do {i <- freshIndex; return (ExistentialTypeVar i, i)}) ns
                        return (apply (Map.fromList $ zip ns $ map fst netvs) t, map snd netvs)



        focus' :: Maybe (String, Type) -> FocusCtxt -> Type -> Synth (Expr, Delta)

        ---- * Right synchronous rules * ------------------

        ---- *R
        focus' Nothing c@(g, d) (Tensor a b) = addtrace (RightTensor c (Tensor a b)) $ do
            (expa, d') <- case a of { ADT _ _ -> focus c a; _ -> focus' Nothing c a }
            (expb, d'') <- case b of { ADT _ _ -> focus (g, d') b; _ -> focus' Nothing (g, d') b }
            return (TensorValue expa expb, d'')

        ---- 1R
        focus' Nothing c@(g, d) Unit = addtrace (RightUnit c) $
            return (UnitValue, d)
            
        ---- +R
        focus' Nothing c (Plus a b) = addtrace (RightPlus c (Plus a b)) $ do
            (il, d') <- case a of { ADT _ _ -> focus c a; _ -> focus' Nothing c a }
            return (InjL (Just b) il, d')
            `interleave` do
            (ir, d') <- case b of { ADT _ _ -> focus c b; _ -> focus' Nothing c b }
            return (InjR (Just a) ir, d')

        ---- sumR
        focus' Nothing c (Sum sts) = addtrace (RightSum (Sum sts)) $
            foldr (interleave . (\(tag, goalt) ->
                do
                   (e, d') <- case goalt of { ADT _ _ -> focus c goalt; _ -> focus' Nothing c goalt }
                   let smts = map (second Just) $ delete (tag, goalt) sts
                   return (SumValue smts (tag, e), d')
                )) empty sts

        ---- adtR
        focus' Nothing c@(g, d) (ADT tyn undefined) = addtrace (RightADT c (ADT tyn undefined)) $ do
            res <- getrestrictions ConstructADT
            guard $ all (\f -> f (ADT tyn undefined)) res
            cons <- getadtcons (ADT tyn undefined)
            foldr (interleave . (\(tag, argty) ->
                addrestriction ConstructADT (ADT tyn undefined) $  -- Cannot construct ADT t as means to construct ADT t -- might cause an infinite loop
                   case argty of
                     Unit -> return (Var tag, d)        -- The branch where this constructor is used might fail later e.g. if an hypothesis isn't consumed from delta when it should have
                     argtype ->
                       if case argtype of
                             ADT tyn' _ -> tyn == tyn'    -- If the constructor for an ADT takes itself as a parameter, focus right should fail and instead focus left. -- TODO: Questionable
                             _ -> False
                          then empty
                          else do
                              (arge, d') <- case argtype of { ADT _ _ -> focus c argtype; _ -> focus' Nothing c argtype }
                              return (App (Var tag) arge, d')
                )) empty cons
            -- When we're right focused, we might continue right focused as we construct the proof (e.g. RightTensor),
            -- However, where other propositions would loop back to asynch mode, and back again to the decision point,
            -- Allowing for a left decision and an eventual instantiation of the goal,
            -- A restricted ADT might fail right away while being right focused, and never considered the possibility of deciding left to instantiate it
            -- Knowning so, all `focus right` expressions will instead just `focus` (and `decide`) on algebraic data types (ADT)s
           

        ---- !R
        focus' Nothing c@(g, d) (Bang a) = addtrace (RightBang c (Bang a)) $ do
            (expa, d') <- synth (g, d, []) a
            guard (d == d')
            return (BangValue expa, d')



        ---- * Left synchronous rules * -------------------

        ---- -oL
        focus' (Just (n, Fun a b)) c@(g, d) goal = addtrace (LeftFun c (Fun a b) goal) $ do
            nname <- fresh
            (expb, d') <- focus' (Just (nname, b)) c goal
            guard (nname `notElem` map fst d')
            (expa, d'') <- synth (g, d', []) a
            return (substitute nname (App (Var n) expa) expb, d'')
            
        ---- &L
        focus' (Just (n, With a b)) c goal = addtrace (LeftWith c (With a b) goal) $
            do
                nname <- fresh
                (lf, d') <- focus' (Just (nname, a)) c goal
                guard (nname `notElem` map fst d')
                return (substitute nname (Fst (Var n)) lf, d')
            <|>
            do
                nname <- fresh
                (rt, d') <- focus' (Just (nname, b)) c goal
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

        -- adtLFocus
        -- if we're focusing left on an ADT X while trying to synth ADT X, instead of decomposing the ADT as we do when inverting rules, we'll instance the var right away -- to tame recursive types
        focus' (Just nh@(n, ADT tyn undefined)) c@(g, d) goal = addtrace (FocusLeftADT c (ADT tyn undefined) goal) $
            if case goal of
              ADT tyn' _ -> tyn' == tyn
              _ -> False
              then return (Var n, d)
              else do
                  adtcns <- getadtcons (ADT tyn undefined) 
                  guard $ not $ null adtcns             -- If the type can't be desconstructed fail here, trying it asynchronously will force another focus/decision of goal -- which under certain circumstances causes an infinite loop
                  res <- getrestrictions DeconstructADT
                  guard $ all (\f -> f (ADT tyn undefined)) res   -- Assert ADT to move to omega can be deconstructed. ADTs that can't would loop back here if they were to be placed in omega
                  synth (g, d, [nh]) goal



        ---- left focus is either atomic or not.
        ---- if it is atomic, it'll either be the goal and instanciate it, or fail
        ---- if it's not atomic, and it's not left synchronous, unfocus

        focus' (Just nh@(n, h)) c@(g, d) goal
          | isAtomic h                      -- left focus is atomic
          = addtrace (DefaultFocusLeft c nh goal) $
          do case goal of
                 (ExistentialTypeVar x)     -- goal is an existential proposition generate a constraint and succeed -- TODO: Fiz isto em vez de ter uma regra para left focus on TypeVar para Existencial porque parece-me que Bool |- ?a tmb deve gerar um constraint ?a => Bool, certo?
                   -> do addconstraint $ Constraint (ExistentialTypeVar x) h
                         return (Var n, d)
                 _ -> do guard (h == goal)  -- if is atomic and not the goal, fail
                         return (Var n, d)  -- else, instantiate it
          | otherwise
          = addtrace (DefaultFocusLeft c nh goal) $ synth (g, d, [nh]) goal         -- left focus is not atomic and not left synchronous, unfocus



        ---- right focus is not synchronous, unfocus. if it is atomic we fail

        focus' Nothing c@(g, d) goal = addtrace (DefaultFocusRight c goal) $
            synth (g, d, []) goal





-------------------------------------------------------------------------------
-- Functions
-------------------------------------------------------------------------------

removeadtcons :: [ADTD] -> (Gamma, Delta) -> (Gamma, Delta)
removeadtcons adts (fc, bc) = case adts of -- During the synth process, constructors should only be used when focused right on the ADT -- so remove them from the unrestricted context
    [] -> (fc, bc)
    (ADTD _ _ cons):xs -> removeadtcons xs (filter (\(n, _) -> isNothing $ lookup n cons) fc, bc)


synthCtxAllType :: (Gamma, Delta) -> Int -> [ADTD] -> Type -> [Expr]
synthCtxAllType c i adts t =
    let c' = removeadtcons adts c in
    let res = runSynth c' t (initSynthState i) adts in
                  if null res
                     then errorWithoutStackTrace $ "[Synth] Failed synthesis of: " ++ show t
                     else map fst res


synthCtxType :: (Gamma, Delta) -> Int -> [ADTD] -> Type -> Expr
synthCtxType c i adts t = head $ synthCtxAllType c i adts t





-------------------------------------------------------------------------------
-- Exported Functions
-------------------------------------------------------------------------------

synthAllType :: Type -> [Expr]
synthAllType = synthCtxAllType ([], []) 0 []


synthType :: Type -> Expr
synthType t = head $ synthAllType $ instantiateFrom 0 $ generalize ([], []) t


synthMarks :: Expr -> [ADTD] -> Expr -- replace all placeholders in an expression with a synthetized expr
synthMarks ex adts = transform transformfunc ex
    where
        transformfunc =
            \case
                (Mark _ name c@(fc, bc) t) -> 
                    let sch@(Forall tvs t') = fromMaybe (error "[Synth] Failed: Marks can't be synthetized without a type.") t in
                    case name of
                      Nothing    -> -- Non-recursive Mark
                        synthCtxType c (length tvs) adts $ instantiateFrom 0 sch
                      Just name' -> -- Recursive Mark
                        case t' of
                          Fun (ADT tyn tps) t2 ->
                              let adtcons = concatMap (\(ADTD _ _ cs) -> cs) $ filter (\(ADTD name _ _) -> tyn == name) adts in
                              let i = length tvs in
                              Abs (getName i) (Just (ADT tyn tps)) $ CaseOf (Var (getName i)) (synthBranches adtcons (i+1))
                              where
                                  synthBranches :: [(Name, Type)] -> Int -> [(String, String, Expr)]
                                  synthBranches adtcons i = map (\(name, vtype) ->
                                        case vtype of
                                          Unit -> do
                                            (name, "", synthCtxType c i adts t2)
                                          argty -> do
                                            (name, getName i, synthCtxType ((name', Left sch):fc, (getName i, argty):(name', instantiateFrom 0 sch):bc) (i+1) adts t2) -- TODO: Inverter ordem fun - hyp ou hyp - fun em delta? vai definir qual é tentado primeiro
                                      ) adtcons
                          _ ->
                              error "[Synth Mark] Recursive mark must be of type ADT a -> b"
                x -> x
                           


-- pre: program has been type inferred
synthMarksModule :: Program -> Program
synthMarksModule (Program adts bs ts cs) = Program adts (map (\(Binding n e) -> Binding n $ synthMarks e adts) bs) ts cs


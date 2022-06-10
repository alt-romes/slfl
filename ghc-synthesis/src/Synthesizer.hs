{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
module Synthesizer (synthesize, synth) where

import Prelude hiding (exp)

import Control.Monad
import Control.Monad.State

import GHC.Core.DataCon
import GHC.Core.TyCo.Rep
import GHC.Core.TyCon
import GHC.Core.Multiplicity
import GHC.Types.Basic (Boxity(Boxed))
import Control.Applicative
import Data.String (fromString)
import GHC.Utils.Outputable (renderWithContext, defaultSDocContext, SDoc, ppr)
import GHC.Tc.Types
-- import GHC.Hs.Dump

import GHC.SourceGen hiding (guard)

-- import Data.Data hiding (TyCon)
import Data.Generics.Aliases (mkT)
import Data.Generics.Schemes (everywhere)

import GHC

import Synthesizer.AST
import Synthesizer.Monad

-- | Run the synthesis from a type and render the resulting expression
--
-- The result is in `TcM` because Type Hole Plugins use this monad and can
-- `SDoc` can be directly used in a raw hole fit
synthesize :: Type -> TcM SDoc
synthesize t = fmap (fromString . renderWithContext defaultSDocContext . ppr) $ runSynth 1 t $ synth t

-- synth' :: Type -> Synth (HsExpr GhcPs)
-- synth' (TyConApp tc l) = do
    -- liftIO $ print (showAstData NoBlankSrcSpan NoBlankEpAnnotations tc)
    -- liftIO $ putStrLn " adding constraint "
    -- solveConstraintsWithEq t t
    -- liftIO $ putStrLn " is equal to itself "
    -- solveConstraintsWithEq t (LitTy $ NumTyLit 5)
    -- liftIO $ putStrLn " is equal to litTy 5 "
    -- f <- fresh
    -- return (bvar f)


-- | Synthesize an expression from a type
synth :: Type -> Synth (HsExpr GhcPs)

---- * Right asynchronous rules * -----------------
---- -oR
synth f@(FunTy _ One a b) = rule "-oR" f $ do
    name <- fresh
    exp <- inOmega (name, a) $ synth b
    guardUsed name
    pure (lambda [bvar name] exp)

---- ->R
synth f@(FunTy x Many a b) = rule "->R" f $ synth (FunTy x One (TyConApp unrestrictedTyCon [a]) b)

-- no more synchronous right propositions, start inverting the ordered context (Ω)

---- * Left asynchronous rules * ------------------

synth t = takeOmegaOr (focus t) $ \case
  (n, tc@(TyConApp c l))

    ---- *L
    | isTupleTyCon c -> rule "*L" (tc =>> t) $ do
        names <- mapM (\tt -> fresh >>= return . (,tt)) l
        exp <- foldr inOmega (synth t) names
        forM_ names (guardUsed . fst)
        return (case' (bvar n) [match [tuple (map (bvar . fst) names)] exp])

    ---- !L
    | consName c == "Ur", [a] <- l -> rule "!L" (tc =>> t) $ do
        name <- fresh
        exp <- inGamma (name, a) $ synth t
        guardUsed name
        return (case' (bvar n) [match [conP "Ur" [bvar name]] exp])

    ---- ADTL
    | isAlgTyCon c -> do
        s <- get
        ruleADTL <|> restoreState s <|> ruleADTLRoundtrip
        where
          ruleADTL = rule "ADTL" (tc =>> t) do
            guardNotRestricted (DeconstructTy tc)
            let dataCons = getInstDataCons c l
            commonDelta <- getDelta
            if null dataCons
               -- An ADT that has no constructors might still be used to
               -- instantiate a proposition, but shouldn't leave synchronous mode
               -- (hence the restriction)
               then addRestriction (DeconstructTy tc) $ pushDelta (n, tc) >> synth t
               else do

                 -- Construct each branch
                 ls <- forMFairConj dataCons $ \(name, ctypes) -> rule ("Deconstruct branch " <> occStr name) (tc =>> t) do
                   -- For recursive types, restrict deconstruction of this type in further computations
                   (if isRecursiveType tc then addRestriction (DeconstructTy tc) else id) do
                     -- Generate a name for each bound type
                     boundNs <- mapM (const fresh) ctypes
                     -- Reset delta for this case branch
                     setDelta commonDelta
                     -- Synth with bound variables; TODO: If type is recursive, allow recursive call?
                     exp <- extendOmega (zip boundNs ctypes) $ synth t
                     -- All resulting deltas must be equal, save it for later
                     delta'  <- getDelta
                     -- Names can't escape bound scope
                     mapM_ guardUsed boundNs
                     -- Return constructor name, bound names, synthesized expression, resulting delta
                     return (name, boundNs, exp, delta')

                 -- Guard all resulting contexts are the same
                 guard $ and $ zipWith (\x y -> t4 x == t4 y) ls (tail ls)
                 return $ case' (bvar n) (map (\(nn, boundNs, exp, _) -> match [ conP (unqual nn) $ map bvar boundNs ] exp) ls)

          ruleADTLRoundtrip = rule "ADTL-Roundtrip" (tc =>> t) do
            -- Only push proposition to delta if the above failure was due to
            -- deconstruction restriction. This allows this proposition to be
            -- used in ways other than deconstruction during focusing
            guardRestricted (DeconstructTy tc)
            pushDelta (n, tc)
            synth t

---- * Synchronous left propositions to Δ * -------
  p -> rule "Move to Δ" (snd p) $ do
      pushDelta p
      synth t



focus :: Type -> Synth (HsExpr GhcPs)
focus fgoal =
    decideLeft fgoal <|> decideRight fgoal <|> decideLeftBang fgoal -- deciding left before right will be correct more often than not (at least based on recent attempts...) -- !TODO: Deciding Right before Left can lead to infinite loops!! (Ex: Expr = Var Nat | Lam Expr)

    where
        decideRight, decideLeft, decideLeftBang :: Type -> Synth (HsExpr GhcPs)

        decideRight goal = do
            s <- get
            handleDecision <|> restoreState s

            where
              handleDecision = rule "Decide-Right" goal $ do
                -- To decide right, goal cannot be atomic
                guardWith "Is Atomic" (not $ isAtomic goal)
                focus' Nothing goal


        decideLeft goal = do
            s <- get
            getDelta >>=
                foldr ((<|>) . (<|> restoreState s) . handleDecision) empty

            where
              handleDecision p =
                rule "Decide-Left" (snd p =>> goal) $
                    delDelta p >> focus' (Just p) goal 

        decideLeftBang goal = do
            s <- get
            getGamma >>=
                foldr ((<|>) . (<|> restoreState s) . handleDecision) empty

            where
              handleDecision p@(n, x) = rule "Decide-Left!" (snd p =>> goal) $ do
                  guardNotRestricted (DecideLeftBangR x goal)
                  -- (if allowrec then id else disallowrecursion) $
                  addRestriction (DecideLeftBangR x goal) $
                      focus' (Just (n, x)) goal


        -- | While focused proposition, synthesize a type
        focus' :: Maybe (SName, Type) -> Type -> Synth (HsExpr GhcPs)

        ---- * Right synchronous rules * ------------------
        focus' Nothing tc@(TyConApp c l)

        ---- *R
            | isTupleTyCon c = rule "*R" tc $ do
                exps <- mapM focusROption l
                return $ ExplicitTuple noAnn (map (Present noAnn . noLocA) exps) Boxed

        ---- !R
            | consName c == "Ur", [a] <- l = rule "!R" tc $ do
                d   <- getDelta
                exp <- synth a
                d'  <- getDelta
                guard (d == d')
                return (var "Ur" @@ exp)

        ---- ADTR
            | isAlgTyCon c = rule "ADTR" tc $ do
                s <- get
                let dataCons = getInstDataCons c l
                foldr ((<|>) . (<|> restoreState s) . (\(tag, args) -> rule ("Construct branch " <> (occStr tag)) tc do

                      -- If the constructor takes no argumments, the restrictions don't matter (the creation of the ADT is trivial).
                      -- Using this constructor might still fail later e.g. if an hypothesis isn't consumed from delta when it should have
                      unless (null args) $
                          guardNotRestricted (ConstructTy tc)

                      -- TODO: If the constructor for an ADT takes just itself as a parameter, focus right should fail and instead focus left.
                      -- if [tc] == args -- TODO: args might not be type instanced yet?
                      --    then trace ("tc in args " <> show (ppr tc)) empty
                      --    else do

                      -- Cannot construct ADT t as means to construct ADT t -- might cause an infinite loop
                      exps <- addRestriction (ConstructTy tc) $ mapM (\t -> rule "Parameter of constructor" t $ focusROption t) args
                      return (foldl (@@) (var (unqual tag)) exps)

                    )) empty dataCons
                -- When we're right focused, we might continue right focused as we construct the proof (e.g. RightTensor),
                -- However, where other propositions would loop back to asynch mode, and back again to the decision point,
                -- Allowing for a left decision and an eventual instantiation of the goal,
                -- A restricted ADT might fail right away while being right focused, and never considered the possibility of deciding left to instantiate it
                -- Knowning so, all `focus right` expressions will instead just `focus` (and `decide`) on algebraic data types (ADT)s


        ---- * Left synchronous rules * -------------------

        ---- VL ROMES:TODO
        -- focusSch (n, ForAllTy ns t) goal = do
        --     -- can only try scheme if current constraints are still safe
        --     -- before trying to synth Unit to use as the instanciation of an existential ?x, make sure this new constraint doesn't violate previous constraints,
        --     -- or else we might try to synth Unit assuming ?x again, which will fail solving the constraints, which in turn will make the Unit try to be synthed again using the other choice which is to assume ?x again...
        --     (et, etvars)  <- existencialInstantiate ns t                    -- tipo com existenciais
        --     (se, d', cs') <- focus' (Just (n, et)) goal                     -- fail ou success c restrições -- sempre que é adicionada uma constraint é feita a unificação
        --                                                                     -- resolve ou falha -- por conflito ou falta informação
        --                                                                     -- por conflicto durante o processo
        --     guard (Set.disjoint (Set.fromList etvars) (ftv $ apply cs' et)) -- por falta de informação (não pode haver variáveis existenciais bound que fiquem por instanciar, i.e. não pode haver bound vars nas ftvs do tipo substituido)
        --                                                                     -- after making sure no instantiated variables escaped, the constraints added to the substitution can be forgotten so that it doesn't complicate further scheme computations
        --     return se                                                       -- if constraints are "total" and satisfiable, the synth using a polymorphic type was successful
        --         where
        --             existencialInstantiate ns t = do
        --                 netvs <- mapM (const $ do {i <- freshIndex; return (ExistentialTypeVar i, -i)}) ns
        --                 return (apply (Map.fromList $ zip ns $ map fst netvs) t, map snd netvs)


        ---- -oL
        focus' (Just (n, f@(FunTy _ One a b))) goal = rule "-oL" (f =>> goal) $ do
            name <- fresh
            expb <- focus' (Just (name, b)) goal
            expa <- synth a
            return (substitute name (bvar n @@ expa) expb)

        ---- ->L
        focus' (Just (n, f@(FunTy x Many a b))) goal = rule "->L" (f =>> goal) $ focus' (Just (n, FunTy x One (TyConApp unrestrictedTyCon [a]) b)) goal

        ---- ∃L (?)
        focus' (Just (n, TyVarTy x)) goal = rule "?L" (TyVarTy x) $
            case goal of
              (TyVarTy y) -> do
                  guard (x == y)  -- ?a |- ?b fails
                  return (bvar n) -- ?a |- ?a succeeds
              _ -> do             -- ?a |- t  succeeds with constraint
                  solveConstraintsWithEq (TyVarTy x) goal
                  return (bvar n)


        ---- * Proposition no longer synchronous * --------

        ---- skip bangs steps
        focus' (Just (n, TyConApp c [t])) (TyConApp goalC [goal])
          | consName c == "Ur" && consName goalC == "Ur" = rule "Skip Bangs" (TyConApp c [t] =>> TyConApp goalC [goal]) $
                focus' (Just (n, t)) goal

        -- -- preemptively instance existential tv goals
        focus' (Just (n, h)) (TyVarTy x) = do
            solveConstraintsWithEq (TyVarTy x) h -- goal is an existential proposition generate a constraint and succeed
            return (bvar n)

        ---- ADTLFocus
        ---- if we're focusing left on an ADT X while trying to synth ADT X, instead of decomposing the ADT as we do when inverting rules, we'll instance the var right away -- to tame recursive types
        focus' (Just nh@(n, tc@(TyConApp c ts))) goal = rule "ADTL-Focus" (tc =>> goal) $ case goal of
          TyConApp c' ts'
            | consName c == consName c'
            -> do
              guard (ts == ts')
              -- TODO: solveConstraintsWithEq (TyConApp c ts) goal
              return (bvar n)
          _ -> do
              let dataCons = getInstDataCons c ts
              -- If the type can't be desconstructed fail here, trying it asynchronously will force another focus/decision of goal -- which under certain circumstances causes an infinite loop
              guard $ not $ null dataCons
              -- Assert ADT to move to omega can be deconstructed. ADTs that
              -- can't would loop back here if they were to be placed in omega
              guardNotRestricted (DeconstructTy (TyConApp c ts))
              inOmega nh $ synth goal

        ---- left focus is either atomic or not.
        ---- if it is atomic, it'll either be the goal and instanciate it, or fail
        ---- if it's not atomic, and it's not left synchronous, unfocus
        focus' (Just nh@(n, h)) goal
          | isAtomic h               -- left focus is atomic
          = do
            guard (h == goal)        -- if is atomic and not the goal, fail
            return (bvar n)          -- else, instantiate it
          | otherwise
          = inOmega nh $ synth goal  -- left focus is not atomic and not left synchronous, unfocus

        -- can't instance type variable when not focused?
        focus' Nothing (TyVarTy _) = empty

        ---- right focus is not synchronous, unfocus.
        focus' Nothing goal = synth goal

        ---- if focus object is synchronous and needs to consider the contexts to be satisfied, focus on a proposition, instead of solely focusing right
        focusROption goal =
            -- TODO: This choice between focus or right focus has potential for errors if we forget cases that should focus (and allow for left decisions) in synchronous propositions that will fail if just focused right,
            -- for example, previously existential variables would be right focused on, and many programs were hidden.
            -- things like refinement types should be considered, right now they aren't contemplated in the process here...
            if case goal of
                TyVarTy _ -> True
                TyConApp c _
                  | isAlgTyCon c && consName c /= "Ur" -> True
                _ -> False
            then
                focus goal
            else
                focus' Nothing goal


isAtomic :: Type -> Bool
isAtomic t =
    case t of
       LitTy _              -> True
       TyVarTy _            -> True
       TyConApp c _
         | isAlgTyCon c     -> False -- ADTs aren't atomic
         | otherwise        -> True  -- TyCons not ADTs are atomic
       _                    -> False


-- | Subsitute var SName with ExpA in ExpB
substitute :: SName -> HsExpr GhcPs -> HsExpr GhcPs -> HsExpr GhcPs
substitute n exp = everywhere (mkT subs)
    where
        subs (HsVar _ i)
          | (rdrNameToStr . unLoc) i == occStr n = exp
        subs e = e


-- | Get the data constructors names and the types of their arguments
--
-- Todo: Infix operators already have parenthesis
getInstDataCons :: TyCon -> [Type] -> [(SName, [Type])]
getInstDataCons tc l = do
    -- Handles substitution of polimorfic types with actual type in constructors
    map (\dc -> ((nameToStr . dataConName) dc, (\(_, _, args) -> args) $ dataConInstSig dc l)) $ tyConDataCons tc


isRecursiveType :: Type -> Bool
isRecursiveType (TyConApp c l) =
    let possibleArgs = concatMap (\dc -> (\(_, _, args) -> args) $ dataConInstSig dc l) $ tyConDataCons c
     in (TyConApp c l) `elem` possibleArgs
isRecursiveType _ = False

-- | Restore the state then fail the computation with `empty`
restoreState :: SynthState -> Synth a
-- hack to restore state
restoreState s = put s >> empty 

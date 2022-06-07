{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
module Synthesizer (synthesize) where

import qualified Data.Map as M
import Control.Monad

import Debug.Trace
import Data.Bifunctor
import GHC.Core.DataCon
import GHC.Core.TyCo.Rep
import GHC.Core.TyCon
import GHC.Core.Multiplicity
import GHC.Types.Basic (Boxity(Boxed))
import Control.Applicative
import GHC.Data.Bag

import GHC.SourceGen hiding (guard)

import Data.Data hiding (TyCon(..))
import Data.Generics.Aliases (mkT)
import Data.Generics.Schemes (everywhere)

import Synthesizer.AST
import Synthesizer.Class

synthesize :: Type -> SDoc
synthesize = ppr . runSynth 3 . synth

synth :: Type -> Synth (HsExpr GhcPs)

---- * Right asynchronous rules * -----------------
---- -oR
synth (FunTy _ One a b) = trace "-oR" $ do
    name <- fresh
    exp <- inOmega (name, a) $ synth b
    guardUsed name
    pure (lambda [bvar name] exp)

---- ->R
synth (FunTy x Many a b) = synth (FunTy x One (TyConApp (dummyTyCon "Ur") [a]) b)

-- no more synchronous right propositions, start inverting the ordered context (Ω)

---- * Left asynchronous rules * ------------------

synth t = takeOmegaOr (trace "focusing!" $ focus t) $ \case
  (n, tc@(TyConApp c l))

    ---- *L
    | isTupleTyCon c -> trace "*L" $ do
        names <- mapM (\t -> fresh >>= return . (,t)) l
        exp <- foldr inOmega (synth t) names
        forM_ names (guardUsed . fst)
        return (case' (bvar n) [match [tuple (map (bvar . fst) names)] exp])

    ---- !L
    | consName c == "Ur" -> trace "!L" $ do
        let [a] = l
        name <- fresh
        exp <- inGamma (name, a) $ synth t
        guardUsed name
        return (case' (bvar n) [match [conP "Ur" [bvar name]] exp])

    ---- ADTL
    | isAlgTyCon c -> trace "ADTL1" (do
        guardNotRestricted DeconstructTy tc
        dataCons    <- getInstDataCons c l
        commonDelta <- getDelta
        if null dataCons
           -- An ADT that has no constructors might still be used to
           -- instantiate a proposition, but shouldn't leave synchronous mode
           -- (hence the restriction)
           then addRestriction DeconstructTy tc $ pushDelta (n, tc) >> synth t
           else do
             -- Construct each branch
             ls <- forMFairConj dataCons $ \(name, ctypes) ->
               (if isRecursiveType tc then addRestriction DeconstructTy tc else id) do
                 -- Generate a name for each bound type
                 boundNs <- mapM (const fresh) ctypes
                 -- Reset delta for this case branch
                 setDelta commonDelta
                 -- Synth
                 exp <- extendOmega (zip boundNs ctypes) $ synth t
                 -- All resulting deltas must be equal, save it for later
                 delta'  <- getDelta
                 -- Names can't escape bound scope
                 traverse guardUsed boundNs
                 -- Return constructor name, bound names, synthesized expression, resulting delta
                 return (name, boundNs, exp, delta')
             -- Guard all resulting contexts are the same
             guard $ and $ zipWith (\x y -> t4 x == t4 y) ls (tail ls)
             return $ case' (bvar n) (map (\(n, boundNs, exp, _) -> match [ conP (unqual n) $ map bvar boundNs ] exp) ls)
        ) <|> trace "ADTL2" (do
            guardRestricted DeconstructTy tc
            pushDelta (n, tc)
            synth t
        )

--     | otherwise -> do
--         error (show (consName c))

---- * Synchronous left propositions to Δ * -------
  p -> trace "move to delta" $ do
      pushDelta p
      synth t



focus :: Type -> Synth (HsExpr GhcPs)
focus goal =
    decideLeft goal <|> decideRight goal <|> decideLeftBang goal -- deciding left before right will be correct more often than not (at least based on recent attempts...) -- !TODO: Deciding Right before Left can lead to infinite loops!! (Ex: Expr = Var Nat | Lam Expr)

    where
        decideRight, decideLeft, decideLeftBang :: Type -> Synth (HsExpr GhcPs)

        decideRight goal =
            if isAtomic goal                            -- to decide right, goal cannot be atomic
                then empty
                else do
                    -- TODO: is possible? to decide right, goal cannot be an ADT that has no constructors
                    -- assertADTHasCons goal >>= guard 
                    focus' Nothing goal

        decideLeft goal = do
            (din, _) <- get
            case din of
              [] -> empty
              _  -> foldr ((<|>) . (\p -> (delDelta p >> focus' (Just p) goal)
                                           <|> (pushDelta p >> empty {- hack to reput deleted delta in state -}))) empty din

        decideLeftBang _ = empty

        -- | While focused proposition, synthesize a type
        focus' :: Maybe (SName, Type) -> Type -> Synth (HsExpr GhcPs)

        ---- * Right synchronous rules * ------------------
        focus' Nothing tc@(TyConApp c l)

        ---- *R
            | isTupleTyCon c = trace "*R" $ do
                exps <- mapM focusROption l
                return $ ExplicitTuple noAnn (map (Present noAnn . noLocA) exps) Boxed

        ---- !R
            | consName c == "Ur" = trace "!R" $ do
                let [a] = l
                d   <- getDelta
                exp <- synth a
                d'  <- getDelta
                guard (d == d')
                return (var "Ur" @@ exp)

        ---- ADTR
            | isAlgTyCon c = trace "ADTR" $ do
                dataCons <- getInstDataCons c l
                foldr ((<|>) . (\(tag, args) -> trace ("Constructor " <> show tag) $ do

                      -- If the constructor takes no argumments, the restrictions don't matter (the creation of the ADT is trivial).
                      -- Using this constructor might still fail later e.g. if an hypothesis isn't consumed from delta when it should have
                      unless (null args) $
                          guardNotRestricted ConstructTy tc

                      -- TODO: If the constructor for an ADT takes just itself as a parameter, focus right should fail and instead focus left.
                      -- if [tc] == args -- TODO: args might not be type instanced yet?
                      --    then trace ("tc in args " <> show (ppr tc)) empty
                      --    else do

                      -- Cannot construct ADT t as means to construct ADT t -- might cause an infinite loop
                      exps <- addRestriction ConstructTy tc $ mapM focusROption args
                      return (foldl (@@) (var (unqual tag)) exps)

                    )) empty dataCons
                -- When we're right focused, we might continue right focused as we construct the proof (e.g. RightTensor),
                -- However, where other propositions would loop back to asynch mode, and back again to the decision point,
                -- Allowing for a left decision and an eventual instantiation of the goal,
                -- A restricted ADT might fail right away while being right focused, and never considered the possibility of deciding left to instantiate it
                -- Knowning so, all `focus right` expressions will instead just `focus` (and `decide`) on algebraic data types (ADT)s


        ---- * Left synchronous rules * -------------------

        ---- -oL
        focus' (Just (n, FunTy _ One a b)) goal = trace "-oL" $ do
            name <- fresh
            expb <- focus' (Just (name, b)) goal
            expa <- synth a
            return (substitute name (bvar n @@ expa) expb)

        ---- ∃L (?)
        focus' (Just (n, TyVarTy x)) goal = trace "?L" $
            case goal of
              (TyVarTy y) ->
                  if x == y then return (bvar n)            -- ?a |- ?a succeeds
                            else empty                      -- ?a |- ?b fails
              _ -> do                                       -- ?a |- t  succeeds with constraint
                  empty


        ---- * Proposition no longer synchronous * --------

        ---- skip bangs steps
        focus' (Just (n, TyConApp c [t])) (TyConApp goalC [goal])
            | consName c == "Ur" && consName goalC == "Ur" =
                focus' (Just (n, t)) goal

        -- -- preemptively instance existential tv goals
        -- focus' (Just nh@(n, h)) (TyVarTy x) = do
            -- TODO: cs' <- addconstraint cs $ Constraint (ExistentialTypeVar x) h -- goal is an existential proposition generate a constraint and succeed
            -- return (bvar n)

        ---- ADTLFocus
        ---- if we're focusing left on an ADT X while trying to synth ADT X, instead of decomposing the ADT as we do when inverting rules, we'll instance the var right away -- to tame recursive types
        focus' (Just nh@(n, TyConApp c ts)) goal = trace "ADTLFocus" $ case goal of
          TyConApp c' ts'
            | isAlgTyCon c' && c == c'
            -> do
              error "llol"
              -- cs' <- addconstraint cs $ Constraint (ADT tyn tps) (ADT tyn' tps')
              -- return (Var n, d, cs')
          _ -> do
              dataCons <- getInstDataCons c ts 
              -- If the type can't be desconstructed fail here, trying it asynchronously will force another focus/decision of goal -- which under certain circumstances causes an infinite loop
              guard $ not $ null dataCons
              -- Assert ADT to move to omega can be deconstructed. ADTs that can't would loop back here if they were to be placed in omega
              guardNotRestricted DeconstructTy (TyConApp c ts)
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
        focus' Nothing (TyVarTy x) = empty

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
       TyConApp c l
         | isAlgTyCon c     -> False -- ADTs aren't atomic
         | otherwise        -> True  -- TyCons not ADTs are atomic
       _                    -> error ("is atom? " <> show (ppr t))


-- | Subsitute var SName with ExpA in ExpB
substitute :: SName -> HsExpr GhcPs -> HsExpr GhcPs -> HsExpr GhcPs
substitute n exp = everywhere (mkT subs)
    where
        subs (HsVar _ id)
          | (rdrNameToStr . unLoc) id == occStr n = exp
        subs e = e


-- | Get the data constructors names and the types of their arguments
--
-- Todo: Infix operators already have parenthesis
getInstDataCons :: TyCon -> [Type] -> Synth [(SName, [Type])]
getInstDataCons tc l = do
    -- Handles substitution of polimorfic types with actual type in constructors
    return $ map (\dc -> ((nameToStr . dataConName) dc, (\(_, _, args) -> args) $ dataConInstSig dc l)) $ tyConDataCons tc


isRecursiveType :: Type -> Bool
isRecursiveType (TyConApp c l) =
    let possibleArgs = concatMap (\dc -> (\(_, _, args) -> args) $ dataConInstSig dc l) $ tyConDataCons c
     in (TyConApp c l) `elem` possibleArgs
isRecursiveType _ = False


-- type Subst = M.Map Int Type

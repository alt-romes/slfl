{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
module Synthesizer (synthesize) where

import qualified Data.Map as M
import Control.Monad

import Debug.Trace
import GHC.Core.TyCo.Rep
import GHC.Core.TyCon
import GHC.Core.Multiplicity
import GHC.Types.Basic (Boxity(Boxed))
import Control.Applicative
import GHC.Data.Bag

import Synthesizer.Class

synthesize :: Type -> SDoc
synthesize = ppr . head . runSynth 1 . synth

synth :: Type -> Synth (HsExpr GhcPs)

---- * Right asynchronous rules * -----------------
---- -oR
synth (FunTy _ One a b) = do
    name <- fresh
    exp <- inOmega (name, a) $ synth b -- todo: this inOmega should append rather than prepend?
    guardUsed name
    pure (lam (VarPat noX (noLocA name)) exp)

-- no more synchronous right propositions, start inverting the ordered context (Ω)

---- * Left asynchronous rules * ------------------
synth t = takeOmega (focus t) $ \case
  (n, TyConApp c l)

    ---- *L
    | consName c == "(,)", [a, b] <- l -> do
        -- TODO: Generalize for tuples with n elements
        (n1, n2) <- (,) <$> fresh <*> fresh
        names <- mapM (\t -> fresh >>= return . (,t)) l
        exp <- foldr inOmega (synth t) names
        guardUsed n1
        guardUsed n2
        return (HsCase noAnn (lvar n)
                (matchGroup
                  (TuplePat noAnn
                      (map (noLocA . VarPat noX . noLocA . fst) names)
                      Boxed)
                  exp))

  p -> do
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
                    -- assertADTHasCons goal >>= guard     -- to decide right, goal cannot be an ADT that has no constructors
                    focus' Nothing goal

        decideLeft goal = do
            (din, _) <- get
            case din of
              [] -> empty
              _  -> foldr ((<|>) . (\p -> (delDelta p >> focus' (Just p) goal)
                                           <|> (pushDelta p >> empty {- hack to replace deleted delta in state -}))) empty din

        decideLeftBang _ = empty

        focus' :: Maybe (RdrName, Type) -> Type -> Synth (HsExpr GhcPs)

        focus' Nothing goal = case goal of
          TyConApp c l
            | consName c == "(,)", [a, b] <- l -> do
                -- TODO: Generalize for tuples with n elements
                expa <- focusROption a
                expb <- focusROption b
                return $ ExplicitTuple noAnn [Present noAnn (noLocA expa), Present noAnn (noLocA expb)] Boxed
          TyVarTy _ -> empty
          _ -> synth goal

        ---- ∃L (?)
        focus' (Just (n, TyVarTy x)) goal =
            case goal of
              (TyVarTy y) ->
                  if x == y then return (var n)             -- ?a |- ?a succeeds
                            else empty                      -- ?a |- ?b fails
              _ -> do                                       -- ?a |- t  succeeds with constraint
                  -- pushDelta (n, TyVarTy x) -- hack to "undo" consume variable
                  empty
                  -- ... Solve constraints and if possible instance with var
                  -- cs' <- addconstraint cs $ Constraint (ExistentialTypeVar x) goal
                  -- return (var n)


        ---- if focus object is synchronous and needs to consider the contexts to be satisfied, focus on a proposition, instead of solely focusing right
        focusROption goal =
            -- TODO: This choice between focus or right focus has potential for errors if we forget cases that should focus (and allow for left decisions) in synchronous propositions that will fail if just focused right,
            -- for example, previously existential variables would be right focused on, and many programs were hidden.
            -- things like refinement types should be considered, right now they aren't contemplated in the process here...
            if case goal of
                -- ADT _ _ -> True
                TyVarTy _ -> True
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
       _                    -> False





-- synth :: IfaceType -> HsExpr SynthPs
-- synth (IfaceLitTy s) = XExpr ()
-- synth (IfaceTyConApp a b) = XExpr ()
-- synth e@(IfaceFunTy {}) = XExpr ()


-- type Ctxt = (Subst, Restrictions, Gamma, Delta, Omega)   -- Delta out is a return value
-- type FocusCtxt = (Subst, Restrictions, Gamma, Delta)     -- Gamma, DeltaIn

-- type Subst = M.Map Int Type

-- type Restriction = Either (Type, Type) Type
-- type Restrictions = [(RestrictTag, Restriction)]


-- data RestrictTag = ConstructADT | DeconstructADT | DecideLeftBangR deriving (Show, Eq, Ord)

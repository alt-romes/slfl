{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
module Synthesizer.Class
    ( module Language.Haskell.Syntax.Expr
    , module Language.Haskell.Syntax.Pat
    , module GHC
    , runState, runReaderT, observeT, observeManyT, asks, get
    , SDoc, ppr
    , module Synthesizer.Class
    ) where

import Debug.Trace
import Data.List
import Data.Either
import Data.Bifunctor
import Control.Applicative
import Control.Monad.Reader
import Control.Monad.State
import Data.Foldable (toList)

import Language.Haskell.Syntax.Pat
import Language.Haskell.Syntax.Expr
import Language.Haskell.Syntax.Extension
import GHC.Utils.Outputable hiding ((<>), empty)
import GHC.Tc.Types.Evidence
import GHC.Tc.Types.Constraint
import GHC.Types.Basic
import GHC.Parser.Annotation
import GHC.Types.Name.Occurrence
import GHC.Types.Name.Reader
import GHC.Types.Name
import GHC.Types.Basic
import GHC.Data.FastString
import GHC.Core.Map.Type
import GHC.Core.TyCon
import GHC.Hs.Pat
import GHC.Tc.Types
import GHC.Core.Coercion
import GHC.Tc.Solver.Interact
import GHC.Tc.Solver.Monad
import GHC.Tc.Utils.Monad
import GHC.Tc.Types.Origin
import GHC.Types.Id
import GHC.Data.Bag
import GHC

import GHC.SourceGen hiding (guard)

import Control.Monad.Logic

import Synthesizer.AST

type SName = OccNameStr

type Prop = (SName, Type)
newtype Gamma = Gamma { gamma :: [Prop] } -- Unrestricted hypothesis                      (Γ)
newtype Delta = Delta { delta :: [Prop] } -- Linear hypothesis (not left asynchronous)    (Δ)
newtype Omega = Omega { omega :: [Prop] } -- Ordered (linear?) hypothesis                 (Ω)

data RestrictTag = ConstructTy Type | DeconstructTy Type | DecideLeftBangR Type Type deriving (Eq)
                   -- Restrictions on construct and deconstruct ADTs, and on deciding left bang on a type to synthesize another type (hence the two type fields)

instance Eq Type where
    -- hack for comparing types using debruijn....
    a == b = deBruijnize a == deBruijnize b

newtype Synth a = Synth { unSynth :: LogicT (ReaderT ([RestrictTag], Gamma, Omega) (StateT (Int, Delta, [Ct]) TcM)) a }
    deriving (Functor, MonadState (Int, Delta, [Ct]), MonadReader ([RestrictTag], Gamma, Omega), Alternative, MonadFail, MonadLogic)

runSynth :: Int -> Type -> Synth a -> TcM [a]
runSynth i t = flip evalStateT (0, Delta mempty, mempty) . flip runReaderT (mempty, Gamma [("rec", trace (show $ ppr t) t)], Omega mempty) . observeManyT i . unSynth

instance Applicative Synth where
    pure = Synth . pure
    (Synth f) <*> (Synth v) = Synth (f <*> v)

instance Monad Synth where
    (Synth a) >>= f = Synth $ a >>= unSynth . f

liftTcM :: TcM a -> Synth a
liftTcM = Synth . lift . lift . lift

-- Synth monad manipulation
-- ========================

-- Add a proposition to the linear context
pushDelta :: Prop -> Synth ()
pushDelta p = modify (first (Delta . (p:) . delta))

delDelta :: Prop -> Synth ()
delDelta p = modify (first (Delta . delete p . delta))

getDelta :: Synth [Prop]
getDelta = do
    (_, d, _) <- get
    return $ delta d

setDelta :: [Prop] -> Synth ()
setDelta = modify . first . const . Delta

-- Take a proposition from the omega context:
--  If one exists, pass it to the 2nd argument (computation using proposition)
--  If none does, run the 1st argument (computation without proposition from omega, basically focus)
--
--  In case a proposition is taken from omega, the computation run won't have it in the omega context anymore
takeOmegaOr :: Synth a -> (Prop -> Synth a) -> Synth a
takeOmegaOr c f = asks (\case (_,_,Omega o) -> o) >>= \case
    (h:o) -> local (second (const (Omega o))) (f h)
    [] -> c

inOmega :: Prop -> Synth a -> Synth a
inOmega nt = local (second (Omega . (<> [nt]) . omega))

extendOmega :: [Prop] -> Synth a -> Synth a
extendOmega o' = local (second (Omega . (<> o') . omega))

inGamma :: Prop -> Synth a -> Synth a
inGamma nt = local (first (Gamma . (<> [nt]) . gamma))

getGamma :: Synth [Prop]
getGamma = do
    (_, g, _) <- ask
    return $ gamma g

getConstraints :: Synth [Ct]
getConstraints = do
    (_, _, cts) <- get
    return cts

setConstraints :: [Ct] -> Synth ()
setConstraints = modify . second . const

addRestriction :: RestrictTag -> Synth a -> Synth a
addRestriction tag = local (\(r,g,o) -> (tag:r, g, o))

guardUsed :: SName -> Synth ()
guardUsed name = do
    d <- getDelta
    guard (name `notElem` map fst d)

guardRestricted :: RestrictTag -> Synth ()
-- guardRestricted (DecideLeftBangR _ _) = undefined
guardRestricted tag = do
    (rs, _, _) <- ask
    guard (tag `elem` rs)

guardNotRestricted :: RestrictTag -> Synth ()
-- ROMES:TODO
-- guardRestricted tag@(DecideLeftBangR _ _) = do
--     (rs, _, _) <- ask
--     existentialdepth <- getExistentialDepth
--     return $ tag `notElem` rs &&
--         -- isExistential => Poly-Exist pairs are less than the existential depth
--         (not (isExistentialType $ snd typair) || existentialdepth > count True (map (\x -> isExistentialType (snd x) && isLeft (fst x)) reslist)) -- no repeated use of unr functions or use of unr func when one was used focused on an existential
guardNotRestricted tag = do
    (rs, _, _) <- ask
    guard (tag `notElem` rs)


-- | Add a constraint to the list of constraints and solve it
-- Failing if the constraints can't be solved with this addition
solveConstraintsWithEq :: Type -> Type -> Synth ()
solveConstraintsWithEq t1 t2 = do
    cts <- getConstraints
    -- Solve the existing constraints with the added equality, failing when unsolvable
    (ct, solved) <- liftTcM $ do
        let predTy = mkPrimEqPred t1 t2
        name <- newName (mkEqPredCoOcc (mkVarOcc "magic"))
        let var = mkVanillaGlobal name predTy
        loc <- getCtLocM (GivenOrigin UnkSkol) Nothing
        let ct = mkNonCanonical $ CtGiven predTy var loc
        ((), EvBindMap evBinds) <- runTcS $ solveSimpleGivens (ct:cts)
        return (ct, not $ null $ toList evBinds)
    guard solved
    setConstraints (ct:cts)

fresh :: Synth SName
fresh = do
    (n, d, cts) <- get
    put (n + 1, d, cts)
    return . occNameToStr . mkVarOcc . getName $ n

    where letters :: [String]
          letters = [1..] >>= flip replicateM ['a'..'z']

          getName :: Int -> String
          getName i = if i < 0 then '-' : letters !! (-i) else letters !! i

forMFairConj :: MonadLogic m => [t] -> (t -> m a) -> m [a]
forMFairConj [] _ = return [] 
forMFairConj (x:xs) f =
  f x >>- \x' -> do
      xs' <- forMFairConj xs f
      return $ x':xs'

t4 :: (a,b,c,d) -> d
t4 (_,_,_,d) = d

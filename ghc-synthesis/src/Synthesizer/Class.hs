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
import Data.Bifunctor
import Control.Applicative
import Control.Monad.Reader
import Control.Monad.State

import Language.Haskell.Syntax.Pat
import Language.Haskell.Syntax.Expr
import Language.Haskell.Syntax.Extension
import GHC.Utils.Outputable hiding ((<>), empty)
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
import GHC

import GHC.SourceGen hiding (guard)

import Control.Monad.Logic

type SName = OccNameStr

type Gamma = [(SName, Type)]       -- Unrestricted hypothesis                      (Γ)
type Delta = [(SName, Type)]       -- Linear hypothesis (not left asynchronous)    (Δ)
type Omega = [(SName, Type)]       -- Ordered (linear?) hypothesis                 (Ω)

type Ctxt = (Gamma, Delta, Omega)   -- Delta out is a return value
type FocusCtxt = (Gamma, Delta)     -- Gamma, DeltaIn


newtype Synth a = Synth { unSynth :: LogicT (ReaderT (Gamma, Omega) (State (Delta, Int))) a }
    deriving (Functor, MonadState (Delta, Int), MonadReader (Gamma, Omega), Alternative, MonadFail)

runSynth :: Int -> Synth a -> [a]
runSynth i = flip evalState (mempty, 0) . flip runReaderT (mempty, mempty) . observeManyT i . unSynth

instance Applicative Synth where
    pure = Synth . pure
    (Synth f) <*> (Synth v) = Synth (f <*> v)

instance Monad Synth where
    (Synth a) >>= f = Synth $ a >>= unSynth . f


-- Synth monad manipulation
-- ========================

-- Add a proposition to the linear context
pushDelta :: (SName, Type) -> Synth ()
pushDelta = modify . first . (:)

delDelta :: (SName, Type) -> Synth ()
-- hack for comparing types using debruijn....
delDelta p = modify (first (\(d :: [(SName, Type)]) -> fmap (\(n, D _ t) -> (n, t)) $ delete (second deBruijnize p) (fmap (second deBruijnize) d)))

-- Take a proposition from the omega context:
--  If one exists, pass it to the 2nd argument (computation using proposition)
--  If none does, run the 1st argument (computation without proposition from omega, basically focus)
--
--  In case a proposition is taken from omega, the computation run won't have it in the omega context anymore
takeOmega :: Synth a -> ((SName, Type) -> Synth a) -> Synth a
takeOmega c f = asks snd >>= \case
    (h:o) -> local (second (const o)) (f h)
    [] -> c

inOmega :: (SName, Type) -> Synth a -> Synth a
inOmega nt = local (second (<> [nt]))

guardUsed :: SName -> Synth ()
guardUsed name = do
    (d, _) <- get
    guard (name `notElem` map fst d)

fresh :: Synth SName
fresh = do
    (c, n) <- get
    put (c, n + 1)
    return . occNameToStr . mkVarOcc . getName $ n

    where letters :: [String]
          letters = [1..] >>= flip replicateM ['a'..'z']

          getName :: Int -> String
          getName i = if i < 0 then '-' : letters !! (-i) else letters !! i


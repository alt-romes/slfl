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

import Synthesizer.AST

type SName = OccNameStr

type Gamma = [(SName, Type)]       -- Unrestricted hypothesis                      (Γ)
type Delta = [(SName, Type)]       -- Linear hypothesis (not left asynchronous)    (Δ)
type Omega = [(SName, Type)]       -- Ordered (linear?) hypothesis                 (Ω)

type Ctxt = (Gamma, Delta, Omega)   -- Delta out is a return value
type FocusCtxt = (Gamma, Delta)     -- Gamma, DeltaIn

type Restrictions = [(RestrictTag, Restriction)]
type Restriction = Either (Type, Type) Type -- Left restriction is on decide left bang proposition, right restriction is on ADT type
data RestrictTag = ConstructTy | DeconstructTy | DecideLeftBangR deriving (Show, Eq, Ord)

instance Eq Type where
    -- hack for comparing types using debruijn....
    a == b = deBruijnize a == deBruijnize b

newtype Synth a = Synth { unSynth :: LogicT (ReaderT (Restrictions, Gamma, Omega) (State (Delta, Int))) a }
    deriving (Functor, MonadState (Delta, Int), MonadReader (Restrictions, Gamma, Omega), Alternative, MonadFail, MonadLogic)

runSynth :: Int -> Synth a -> [a]
runSynth i = flip evalState (mempty, 0) . flip runReaderT (mempty, mempty, mempty) . observeManyT i . unSynth

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
delDelta p = modify (first (delete p))

getDelta :: Synth Delta
getDelta = get >>= return . fst

setDelta :: Delta -> Synth ()
setDelta = modify . first . const

-- Take a proposition from the omega context:
--  If one exists, pass it to the 2nd argument (computation using proposition)
--  If none does, run the 1st argument (computation without proposition from omega, basically focus)
--
--  In case a proposition is taken from omega, the computation run won't have it in the omega context anymore
takeOmegaOr :: Synth a -> ((SName, Type) -> Synth a) -> Synth a
takeOmegaOr c f = asks (\case (_,_,o) -> o) >>= \case
    (h:o) -> local (second (const o)) (f h)
    [] -> c

inOmega :: (SName, Type) -> Synth a -> Synth a
inOmega nt = local (second (<> [nt]))

extendOmega :: Omega -> Synth a -> Synth a
extendOmega o' = local (second (<> o'))

inGamma :: (SName, Type) -> Synth a -> Synth a
inGamma nt = local (first (<> [nt]))

addRestriction :: RestrictTag -> Type -> Synth a -> Synth a
addRestriction tag ty = local (\(r,g,o) -> ((tag, Right ty):r, g, o))

guardUsed :: SName -> Synth ()
guardUsed name = do
    (d, _) <- get
    guard (name `notElem` map fst d)

guardRestricted :: RestrictTag -> Type -> Synth ()
guardRestricted tag tc = do -- Restrictions only on ADT Construction and Destruction
    (rs, _, _) <- ask
    let f = rights . map snd . filter ((== tag) . fst)
    guard (not $ tc `notElem` f rs)

guardNotRestricted :: RestrictTag -> Type -> Synth ()
guardNotRestricted tag tc = do -- Restrictions only on ADT Construction and Destruction
    (rs, _, _) <- ask
    let f = rights . map snd . filter ((== tag) . fst)
    guard (tc `notElem` f rs) -- what is this: && (not (isExistentialType ty) || not (any isExistentialType $ filter (\(ADT tyn' _) -> tyn == tyn') reslist))

fresh :: Synth SName
fresh = do
    (c, n) <- get
    put (c, n + 1)
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

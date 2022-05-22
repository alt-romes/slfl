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
import GHC.Hs.Pat
import GHC

import Control.Monad.Logic


type Gamma = [(RdrName, Type)]       -- Unrestricted hypothesis                      (Γ)
type Delta = [(RdrName, Type)]       -- Linear hypothesis (not left asynchronous)    (Δ)
type Omega = [(RdrName, Type)]       -- Ordered (linear?) hypothesis                 (Ω)

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


var :: RdrName -> HsExpr GhcPs
var n = HsVar noX (noLocA n)

lvar :: RdrName -> LHsExpr GhcPs
lvar = noLocA . var

lam :: Pat GhcPs -> HsExpr GhcPs -> HsExpr GhcPs
lam p b = HsLam noExtField (matchGroup p b)

match :: Pat GhcPs -> HsExpr GhcPs -> Match GhcPs (LHsExpr GhcPs)
match p b = Match noAnn LambdaExpr [noLocA p] (aGRHSs b)

matchGroup :: Pat GhcPs -> HsExpr GhcPs -> MatchGroup GhcPs (LHsExpr GhcPs)
matchGroup p b = MG noX (noLocA [noLocA (match p b)]) Generated

aGRHSs :: HsExpr GhcPs -> GRHSs GhcPs (LHsExpr GhcPs)
aGRHSs b = (GRHSs (comments noAnn) [noLoc $ GRHS noAnn [] (noLocA b)] (EmptyLocalBinds noExtField))

-- aGRHSs' :: HsExpr GhcPs -> GRHSs GhcPs (LHsExpr GhcPs)
-- aGRHSs' b = trace (show ppr $ aGRHSs b) (aGRHSs b)

noX :: NoExtField
noX = noExtField

consName :: TyCon -> FastString
consName = occNameFS . nameOccName . getName


-- Synth monad manipulation
-- ========================

-- Add a proposition to the linear context
pushDelta :: (RdrName, Type) -> Synth ()
pushDelta = modify . first . (:)

delDelta :: (RdrName, Type) -> Synth ()
-- hack for comparing types using debruijn....
delDelta p = modify (first (\(d :: [(RdrName, Type)]) -> fmap (\(n, D _ t) -> (n, t)) $ delete (second deBruijnize p) (fmap (second deBruijnize) d)))

-- Take a proposition from the omega context:
--  If one exists, pass it to the 2nd argument (computation using proposition)
--  If none does, run the 1st argument (computation without proposition from omega, basically focus)
--
--  In case a proposition is taken from omega, the computation run won't have it in the omega context anymore
takeOmega :: Synth a -> ((RdrName, Type) -> Synth a) -> Synth a
takeOmega c f = asks snd >>= \case
    (h:o) -> local (second (const o)) (f h)
    [] -> c

inOmega :: (RdrName, Type) -> Synth a -> Synth a
inOmega nt = local (second (<> [nt]))

guardUsed :: RdrName -> Synth ()
guardUsed name = do
    (d, _) <- get
    guard (name `notElem` map fst d)

fresh :: Synth RdrName
fresh = do
    (c, n) <- get
    put (c, n + 1)
    return . mkRdrUnqual . mkVarOcc . getName $ n

    where letters :: [String]
          letters = [1..] >>= flip replicateM ['a'..'z']

          getName :: Int -> String
          getName i = if i < 0 then '-' : letters !! (-i) else letters !! i


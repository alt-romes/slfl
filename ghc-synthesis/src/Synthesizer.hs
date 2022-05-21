{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
module Synthesizer (synthesize) where

import qualified Data.Map as M
import Control.Monad

import GHC.Core.TyCo.Rep
import GHC.Core.Multiplicity
-- import GHC.CoreToIface
-- import GHC.Iface.Type
import GHC.Utils.Outputable

import Synthesizer.Ext

newtype Synth a = Synth a
    deriving Functor

instance Applicative Synth where
    pure = Synth
    (Synth f) <*> (Synth v) = Synth (f v)

runSynth (Synth x) = x

type Gamma = [(Name, Type)]       -- Unrestricted hypothesis                      (Γ)
type Delta = [(Name, Type)]       -- Linear hypothesis (not left asynchronous)    (Δ)
type Omega = [(Name, Type)]       -- Ordered (linear?) hypothesis                 (Ω)

type Ctxt = (Gamma, Delta, Omega)   -- Delta out is a return value
type FocusCtxt = (Gamma, Delta)     -- Gamma, DeltaIn

synthesize :: Type -> SDoc
synthesize = ppr . runSynth . synth

synth :: Type -> Synth (HsExpr SynthPs)
synth (FunTy _ One a b) =
    pure $ lam (match (VarPat () (I "hi")) (XExpr ()))

---- * Right asynchronous rules * -----------------










letters :: [String]
letters = [1..] >>= flip replicateM ['a'..'z']

getName :: Int -> String
getName i = if i < 0 then '-' : letters !! (-i) else letters !! i






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

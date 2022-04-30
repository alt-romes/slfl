{-# LANGUAGE OverloadedStrings #-}
module Synthesizer (synthesize) where

import GHC.Core.TyCo.Rep
import GHC.CoreToIface
import GHC.Iface.Type
import GHC.Utils.Outputable

synthesize :: Type -> SDoc
synthesize = synth . toIfaceType

synth :: IfaceType -> SDoc
synth (IfaceLitTy s) = ppr s
synth (IfaceTyConApp a b) = ppr a <+> "and" <+> ppr b

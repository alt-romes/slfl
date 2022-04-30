module Synthesizer (synthesize) where

import GHC.Core.TyCo.Rep

synthesize :: Type -> Type
synthesize = id

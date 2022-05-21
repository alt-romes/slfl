{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
module Synthesizer.Ext (module Language.Haskell.Syntax.Expr, module Language.Haskell.Syntax.Pat, module Synthesizer.Ext) where

import Language.Haskell.Syntax.Pat
import Language.Haskell.Syntax.Expr
import Language.Haskell.Syntax.Extension
import GHC.Utils.Outputable
import GHC

data SynthPs

data I a = I a

type instance XRec SynthPs p = I p

-- Exp
type instance XMG SynthPs a = ()
type instance XXGRHSs SynthPs b = b
type instance XCMatch SynthPs a = ()
type instance XLam SynthPs = ()
type instance XXExpr SynthPs = ()

-- Pat
type instance XVarPat SynthPs = ()

instance Outputable (HsExpr SynthPs) where
    ppr (XExpr ()) = "romes"
    ppr (_) = "romes"

type instance IdP SynthPs = RdrName

lam :: Match SynthPs (I (HsExpr SynthPs)) -> HsExpr GhcPs
lam x = HsLam () (MG () (I [I x]) Generated)

match :: Pat SynthPs -> HsExpr SynthPs -> Match SynthPs (I (HsExpr SynthPs))
match p b = Match () LambdaExpr [I p] (XGRHSs (I b))

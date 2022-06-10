{-# LANGUAGE OverloadedStrings #-}
module Synthesizer.Plugin where

import Prelude hiding ((<>))

import GHC.Plugins hiding ((<>))
import GHC.Tc.Types.Constraint
import Data.IORef (newIORef)

import Synthesizer (synthesize)

fromPureHFPlugin :: HoleFitPlugin -> HoleFitPluginR
fromPureHFPlugin plug =
  HoleFitPluginR { hfPluginInit = liftIO $ newIORef ()
                 , hfPluginRun = const plug
                 , hfPluginStop = const $ return () }

plugin :: Plugin
plugin = defaultPlugin { holeFitPlugin = hfp }

hfp :: [CommandLineOption] -> Maybe HoleFitPluginR
hfp _ = Just (fromPureHFPlugin $ HoleFitPlugin cp fp)

cp :: CandPlugin
cp _ cands = return cands

fp :: FitPlugin
fp thole hfs =
  case th_hole thole of
    Just hole
      | ty <- hole_ty hole 
      -> do
        synthesized_exp <- synthesize ty
        return $ (RawHoleFit ("" $+$ "Synthesized solution:" $+$ (synthesized_exp) $+$ ""):hfs)
    _ -> return hfs


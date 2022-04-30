module Plugin where

import GHC.Plugins
import GHC.Tc.Errors.Hole
import GHC.Tc.Errors.Hole.FitTypes
import GHC.Tc.Types.Constraint
import Data.IORef (newIORef)

fromPureHFPlugin :: HoleFitPlugin -> HoleFitPluginR
fromPureHFPlugin plug =
  HoleFitPluginR { hfPluginInit = liftIO $ newIORef ()
                 , hfPluginRun = const plug
                 , hfPluginStop = const $ return () }


plugin :: Plugin
plugin = defaultPlugin { holeFitPlugin = hfp }

hfp :: [CommandLineOption] -> Maybe HoleFitPluginR
hfp opts = Just (fromPureHFPlugin $ HoleFitPlugin cp fp)

cp :: CandPlugin
cp thole cands =
  case th_hole thole of
    Just hole
      | ty <- hole_ty hole
      -> error (showSDocUnsafe $ ppr ty)

    _ -> return cands

fp :: FitPlugin
-- fp ("hoogle":[]) hole hfs =
    -- do dflags <- getDynFlags
    --    let tyString = showSDoc dflags . ppr . ctPred <$> tyHCt hole
    --    res <- case tyString of
    --             Just ty -> liftIO $ searchHoogle ty
    --             _ -> return []
    --    return $ (take 2 $ map (RawHoleFit . text . ("Hoogle says: " ++)) res) ++ hfs
fp _ hfs = return hfs


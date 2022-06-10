{-# LANGUAGE LambdaCase #-}
module Synthesizer.AST where

import GHC.Types.Name.Occurrence
import GHC.Types.Name.Reader
import GHC.Types.Name
import GHC.Core.Type
import GHC.Core.TyCon
import GHC.Core.DataCon
import GHC.Types.Unique

import GHC.SourceGen

consName :: TyCon -> String
consName = occNameStrToString . nameToStr . getName

rdrNameToStr :: RdrName -> String
rdrNameToStr = occNameStrToString . occNameToStr . rdrNameOcc

occStr :: OccNameStr -> String
occStr = occNameStrToString

-- | Create a dummy data con -- the only "real" value is the name
dummyDataCon :: String -> DataCon
dummyDataCon na = mkDataCon (dummyName na) False (dummyName na) [] [] [] [] [] [] undefined [] undefined undefined undefined undefined undefined undefined undefined

dummyName :: String -> Name
dummyName = mkSystemName (mkUniqueGrimily 0) . mkVarOcc

unrestrictedTyCon :: TyCon
unrestrictedTyCon = mkAlgTyCon (dummyName "Ur") [] liftedTypeKind [] Nothing [] (DataTyCon [dummyDataCon "Ur"] 1 False) (VanillaAlgTyCon $ dummyName "Ur") False

dummyTyCon :: String -> TyCon
dummyTyCon x = mkAlgTyCon (dummyName x) [] liftedTypeKind [] Nothing [] AbstractTyCon (VanillaAlgTyCon $ dummyName x) False


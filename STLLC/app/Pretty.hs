module Pretty (Pretty(..), parensIf) where

import Text.PrettyPrint



-------------------------------------------------------------------------------
-- Pretty
-------------------------------------------------------------------------------

class Pretty p where
    ppr :: Int -> p -> Doc

    pp :: p -> Doc
    pp = ppr 0





-------------------------------------------------------------------------------
-- Functions
-------------------------------------------------------------------------------

parensIf :: Bool -> Doc -> Doc
parensIf True = parens
parensIf False = id


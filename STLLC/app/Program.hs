module Program where

import CoreSyntax
import Syntax



data Program = Program [ADT] [Binding]

data CoreProgram = CoreProgram [ADT] [CoreBinding]

data ADT = ADT Name [(Name, Type)]    -- Algebric Data Type





instance Show Program where
    show (Program adts bs) = unlines (map show adts) ++ unlines (map show bs)

instance Show CoreProgram where
    show (CoreProgram adts bs) = unlines (map show adts) ++ unlines (map show bs)

instance Show ADT where
    show (ADT n ((c, t):cs)) = "data " ++ n ++ " = " ++ c ++ showType t ++ foldl (\p (c', t') -> p ++ " | " ++ c' ++ showType t') "" cs
        where
            showType t = if t == Unit then "" else " " ++ show t

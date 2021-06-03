module Program where

import CoreSyntax
import Syntax



data Program = Program [ADT] [Binding]

data CoreProgram = CoreProgram [ADT] [CoreBinding]

data ADT = ADT Name [(Name, Type)]    -- Algebric Data Type





instance Show Program where
    show (Program adts bs) = show adts ++ show bs

instance Show CoreProgram where
    show (CoreProgram adts bs) = show adts ++ show bs

instance Show ADT where
    show (ADT n ((c, t):cs)) = "data " ++ n ++ " = " ++ show c ++ " " ++ show t ++ foldl (\p (c', t') -> p ++ " | " ++ show c' ++ " " ++ show t') "" cs

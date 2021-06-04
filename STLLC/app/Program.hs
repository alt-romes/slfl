module Program where

import CoreSyntax
import Syntax



data Program = Program [ADTD] [Binding]

data CoreProgram = CoreProgram [ADTD] [CoreBinding]

data ADTD = ADTD Name [(Name, Type)]    -- Algebraic Data Type Definition
-- TODO: validar (no desugaring ou no typechecker) nao há construtores recursivos, tipos estão bem formados, tipos diferentes têm construtores diferentes...
-- TODO: para tipos recursivos fazer validação tendo em conta que nome do ADT pode ser usado como tipo nos construtores




instance Show Program where
    show (Program adts bs) = unlines (map show adts) ++ unlines (map show bs)

instance Show CoreProgram where
    show (CoreProgram adts bs) = unlines (map show adts) ++ unlines (map show bs)

instance Show ADTD where
    show (ADTD n ((c, t):cs)) = "data " ++ n ++ " = " ++ c ++ showType t ++ foldl (\p (c', t') -> p ++ " | " ++ c' ++ showType t') "" cs
        where
            showType t = if t == Unit then "" else " " ++ show t

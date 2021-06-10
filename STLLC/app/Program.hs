{-# LANGUAGE LambdaCase #-}
module Program (Program(..), CoreProgram(..), ADTD(..), copyMarksTypesModule) where

import qualified Data.Map as Map


import CoreSyntax
import Syntax


-------------------------------------------------------------------------------
-- Datatypes
-------------------------------------------------------------------------------

data Program = Program [ADTD] [Binding]


data CoreProgram = CoreProgram [ADTD] [CoreBinding]


-- TODO: validar (no desugaring ou no typechecker) nao há construtores recursivos, tipos estão bem formados, tipos diferentes têm construtores diferentes...
data ADTD = ADTD Name [(Name, Type)]    -- Algebraic Data Type Definition





-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance Show Program where
    show (Program adts bs) = unlines (map show adts) ++ unlines (map show bs)


instance Show CoreProgram where
    show (CoreProgram adts bs) = unlines (map show adts) ++ unlines (map show bs)


instance Show ADTD where
    show (ADTD n ((c, t):cs)) = "data " ++ n ++ " = " ++ c ++ showType t ++ foldl (\p (c', t') -> p ++ " | " ++ c' ++ showType t') "" cs
        where
            showType t = if t == Unit then "" else " " ++ show t





-------------------------------------------------------------------------------
-- Functions
-------------------------------------------------------------------------------

type MarksTypes = Map.Map Int ([(String, Scheme)], Maybe Type)

copyMarksTypesModule :: Program -> CoreProgram -> Program
copyMarksTypesModule (Program adts bs) (CoreProgram _ cbs) = Program adts $ zipWith copyMarksTypes bs cbs
    where
        -- copy marks types to the non-desugared expression from the desugared+inferred expression
        copyMarksTypes :: Binding -> CoreBinding -> Binding
        copyMarksTypes (Binding n e) (CoreBinding _ ce) = Binding n $ copyMarksTypes' (getMarksTypes Map.empty ce) e
            where
                getMarksTypes :: MarksTypes -> CoreExpr -> MarksTypes
                getMarksTypes m (CoreSyntax.Mark i c t) = Map.insert i (c,t) m
                getMarksTypes m (CoreSyntax.Abs _ e) = getMarksTypes m e
                getMarksTypes m (CoreSyntax.App e e') = getMarksTypes m e `Map.union` getMarksTypes m e'
                getMarksTypes m (CoreSyntax.TensorValue e e') = getMarksTypes m e `Map.union` getMarksTypes m e'
                getMarksTypes m (CoreSyntax.LetTensor e e') = getMarksTypes m e `Map.union` getMarksTypes m e'
                getMarksTypes m (CoreSyntax.LetUnit e e') = getMarksTypes m e `Map.union` getMarksTypes m e'
                getMarksTypes m (CoreSyntax.WithValue e e') = getMarksTypes m e `Map.union` getMarksTypes m e'
                getMarksTypes m (CoreSyntax.Fst e) = getMarksTypes m e
                getMarksTypes m (CoreSyntax.Snd e) = getMarksTypes m e
                getMarksTypes m (CoreSyntax.InjL _ e) = getMarksTypes m e
                getMarksTypes m (CoreSyntax.InjR _ e) = getMarksTypes m e
                getMarksTypes m (CoreSyntax.CaseOfPlus e e' e'') = getMarksTypes m e `Map.union` getMarksTypes m e' `Map.union` getMarksTypes m e''
                getMarksTypes m (CoreSyntax.BangValue e) = getMarksTypes m e
                getMarksTypes m (CoreSyntax.LetIn e e') = getMarksTypes m e `Map.union` getMarksTypes m e'
                getMarksTypes m a = m

                copyMarksTypes' :: MarksTypes -> Expr -> Expr
                copyMarksTypes' m e =
                    Syntax.transform (\case
                        (Syntax.Mark i _ t) -> let (c, t) = Map.findWithDefault (error "[Copy Marks Types] Failed to find mark index in map, make sure to use the same expression desugared and non-desugared when copying marks types.") i m in Syntax.Mark i c t;
                         x -> x) e


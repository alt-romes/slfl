{-# LANGUAGE LambdaCase #-}
module Program (Program(..), ADTD(..), trivialProgram, completeFrontendMarksCtx) where

import qualified Data.Map as Map


import CoreSyntax
import Syntax



-------------------------------------------------------------------------------
-- Datatypes
-------------------------------------------------------------------------------

data Program = Program
    { _adts     :: [ADTD]
    , _binds    :: [Binding]
    , _tbinds   :: [TypeBinding]
    , _cbinds   :: [CoreBinding]
    }


-- TODO: validar (no desugaring ou no typechecker) nao há construtores recursivos, tipos estão bem formados, tipos diferentes têm construtores diferentes...
data ADTD = ADTD Name [(Name, Type)]    -- Algebraic Data Type Definition





-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance Show Program where
    show (Program adts bs ts cs) = unlines (map show adts) ++ unlines (map show bs) ++ unlines (map show ts) ++ unlines (map show cs)


instance Show ADTD where
    show (ADTD n ((c, t):cs)) = "data " ++ n ++ " = " ++ c ++ showType t ++ foldl (\p (c', t') -> p ++ " | " ++ c' ++ showType t') "" cs
        where
            showType t = if t == Unit then "" else " " ++ show t





-------------------------------------------------------------------------------
-- Functions
-------------------------------------------------------------------------------

trivialProgram :: Program
trivialProgram = Program [] [] [] []


type MarksTypes = Map.Map Int (([(String, Either Scheme Type)], [(String, Type)]), Maybe Type)

-- | Copy the Marks info from the core bindings to the syntax bindings marks by id
completeFrontendMarksCtx :: Program -> Program
completeFrontendMarksCtx (Program as bs ts cs) =                    -- !TODO: É impossível copiar as Marks de um lado para o outro por não saber os nomes usados nos binders.
                                                                    --        Conclusão: Seria preciso fazer um typechecker para a frontend Syntax
        Program as (zipWith copyMarksTypes bs cs) ts cs
        where
                -- copy marks types to the non-desugared expression from the desugared+inferred expression
                copyMarksTypes :: Binding -> CoreBinding -> Binding
                copyMarksTypes (Binding n e) (CoreBinding _ ce) = Binding n $ copyMarksTypes' (getMarksTypes Map.empty ce) e
                    where
                        getMarksTypes :: MarksTypes -> CoreExpr -> MarksTypes
                        getMarksTypes m (CoreSyntax.Mark i c t) = --Map.insert i (c,t) m
                            Map.insert i (adaptmc c, t) m
                                where
                                    adaptmc (bc, fc) = (map (\(n,s) -> case s of
                                                                         Forall [] t -> (n, Right t)
                                                                         s' -> (n, Left s')
                                                       ) fc, []) -- Preciso fazer typechecker para a frontend se quiser usar o bound context....
                            
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
                        getMarksTypes m (CoreSyntax.SumValue _ (n, e)) = getMarksTypes m e
                        getMarksTypes m (CoreSyntax.CaseOfSum e ls) = getMarksTypes m e `Map.union` foldr (Map.union . getMarksTypes m . snd) Map.empty ls
                        getMarksTypes m (CoreSyntax.CaseOf e ls) = getMarksTypes m e `Map.union` foldr (Map.union . getMarksTypes m . snd) Map.empty ls
                        getMarksTypes m a = m


                        copyMarksTypes' :: MarksTypes -> Expr -> Expr
                        copyMarksTypes' m e =
                            Syntax.transform (\case
                                (Syntax.Mark i _ _) -> let (c, t') = Map.findWithDefault (error "[Copy Marks Types] Failed to find mark index in map") i m
                                                        in Syntax.Mark i c t';
                                 x -> x) e


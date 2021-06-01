{-# LANGUAGE LambdaCase #-}
module Util where
    
import CoreSyntax
import Syntax

import qualified Data.Map as Map

findDelete :: (Eq a) => a -> [(a, b)] -> [(a, b)] -> (Maybe b, [(a, b)])
findDelete _ [] _ = (Nothing, [])
findDelete x ((y,t):xs) acc =
    if x==y then (Just t, reverse acc ++ xs)
    else findDelete x xs ((y,t):acc)

type MarksTypes = Map.Map Int (Maybe Type)

-- copy marks types to the non-desugared expression from the desugared+inferred expression
copyMarksTypes :: Binding -> CoreBinding -> Binding
copyMarksTypes (Binding n e) (CoreBinding _ ce) = Binding n $ copyMarksTypes' (getMarksTypes Map.empty ce) e
    where
        getMarksTypes :: MarksTypes -> CoreExpr -> MarksTypes
        getMarksTypes m (CoreSyntax.Mark i t) = Map.insert i t m
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
        getMarksTypes m (CoreSyntax.IfThenElse e e' e'') = getMarksTypes m e `Map.union` getMarksTypes m e' `Map.union` getMarksTypes m e''
        getMarksTypes m a = m

        copyMarksTypes' :: MarksTypes -> Expr -> Expr
        copyMarksTypes' m t = editexp (\case {Syntax.Mark _ _ -> True; _ -> False}) (\(Syntax.Mark i t) -> Syntax.Mark i $ Map.findWithDefault (error "[Copy Marks Types] Failed to find mark index in map, make sure to use the same expression desugared and non-desugared when copying marks types.") i m) t 


copyMarksTypesModule :: [Binding] -> [CoreBinding] -> [Binding]
copyMarksTypesModule = zipWith copyMarksTypes



---- Apply a function to edit certain expression constructors arbitrarily deep in the expression
-- TODO : http://dev.stephendiehl.com/fun/007_path.html#traversals
-- Nota: Não consegui o above ^^^
editexp :: (Expr -> Bool) -> (Expr -> Expr) -> Expr -> Expr
editexp c f e = if c e then f e else editexp' c f e
    where
        editexp' c f (Syntax.Abs x t e) = Syntax.Abs x t $ editexp c f e
        editexp' c f (Syntax.App e1 e2) = Syntax.App (editexp c f e1) (editexp c f e2)
        editexp' c f (Syntax.TensorValue e1 e2) = Syntax.TensorValue (editexp c f e1) (editexp c f e2)
        editexp' c f (Syntax.LetTensor u v e1 e2) = Syntax.LetTensor u v (editexp c f e1) (editexp c f e2)
        editexp' c f (Syntax.LetUnit e1 e2) = Syntax.LetUnit (editexp c f e1) (editexp c f e2)
        editexp' c f (Syntax.WithValue e1 e2) = Syntax.WithValue (editexp c f e1) (editexp c f e2)
        editexp' c f (Syntax.Fst e) = Syntax.Fst $ editexp c f e
        editexp' c f (Syntax.Snd e) = Syntax.Snd $ editexp c f e
        editexp' c f (Syntax.InjL t e) = Syntax.InjL t $ editexp c f e
        editexp' c f (Syntax.InjR t e) = Syntax.InjR t $ editexp c f e
        editexp' c f (Syntax.CaseOfPlus e1 x e2 y e3) = Syntax.CaseOfPlus (editexp c f e1) x (editexp c f e2) y (editexp c f e3)
        editexp' c f (Syntax.BangValue e) = Syntax.BangValue (editexp c f e)
        editexp' c f (Syntax.LetBang x e1 e2) = Syntax.LetBang x (editexp c f e1) (editexp c f e2)
        editexp' c f (Syntax.IfThenElse e1 e2 e3) = Syntax.IfThenElse (editexp c f e1) (editexp c f e2) (editexp c f e3)
        editexp' c f (Syntax.LetIn x e1 e2) = Syntax.LetIn x (editexp c f e1) (editexp c f e2)
        editexp' c f e = e      -- atomic expressions

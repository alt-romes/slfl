module Util where
    
import CoreSyntax
import Syntax

---- Apply a function to edit certain expression constructors arbitrarily deep in the expression

-- TODO: Tentei, mas não percebi se aqui podia ser um functor, porque estou a iterar toda a árvore, mas como tenho o fmap seria (a -> a) -> a -> a, em vez de -> f a -> f a (porque faria o Expr ser instance of Functor certo ?) não parecia funcionar

editexp :: (Expr -> Bool) -> (Expr -> Expr) -> Expr -> Expr
editexp c f e = if c e then f e else editexp' c f e         -- POSSIBLE TODO: Refactor to remove condition?
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

editcoreexp :: (CoreExpr -> Bool) -> (CoreExpr -> CoreExpr) -> CoreExpr -> CoreExpr
editcoreexp c f e = if c e then f e else editcoreexp' c f e
    where
        editcoreexp' c f (CoreSyntax.Abs t e) = CoreSyntax.Abs t $ editcoreexp c f e
        editcoreexp' c f (CoreSyntax.App e1 e2) = CoreSyntax.App (editcoreexp c f e1) (editcoreexp c f e2)
        editcoreexp' c f (CoreSyntax.TensorValue e1 e2) = CoreSyntax.TensorValue (editcoreexp c f e1) (editcoreexp c f e2)
        editcoreexp' c f (CoreSyntax.LetTensor e1 e2) = CoreSyntax.LetTensor (editcoreexp c f e1) (editcoreexp c f e2)
        editcoreexp' c f (CoreSyntax.LetUnit e1 e2) = CoreSyntax.LetUnit (editcoreexp c f e1) (editcoreexp c f e2)
        editcoreexp' c f (CoreSyntax.WithValue e1 e2) = CoreSyntax.WithValue (editcoreexp c f e1) (editcoreexp c f e2)
        editcoreexp' c f (CoreSyntax.Fst e) = CoreSyntax.Fst $ editcoreexp c f e
        editcoreexp' c f (CoreSyntax.Snd e) = CoreSyntax.Snd $ editcoreexp c f e
        editcoreexp' c f (CoreSyntax.InjL t e) = CoreSyntax.InjL t $ editcoreexp c f e
        editcoreexp' c f (CoreSyntax.InjR t e) = CoreSyntax.InjR t $ editcoreexp c f e
        editcoreexp' c f (CoreSyntax.CaseOfPlus e1 e2 e3) = CoreSyntax.CaseOfPlus (editcoreexp c f e1) (editcoreexp c f e2) (editcoreexp c f e3)
        editcoreexp' c f (CoreSyntax.BangValue e) = CoreSyntax.BangValue (editcoreexp c f e)
        editcoreexp' c f (CoreSyntax.LetBang e1 e2) = CoreSyntax.LetBang (editcoreexp c f e1) (editcoreexp c f e2)
        editcoreexp' c f (CoreSyntax.IfThenElse e1 e2 e3) = CoreSyntax.IfThenElse (editcoreexp c f e1) (editcoreexp c f e2) (editcoreexp c f e3)
        editcoreexp' c f (CoreSyntax.LetIn e1 e2) = CoreSyntax.LetIn (editcoreexp c f e1) (editcoreexp c f e2)
        editcoreexp' c f e = e      -- atomic expressions

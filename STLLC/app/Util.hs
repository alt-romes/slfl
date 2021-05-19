module Util where
    
import CoreSyntax
import Syntax

---- Apply a function to edit certain expression constructors arbitrarily deep in the expression

-- TODO : http://dev.stephendiehl.com/fun/007_path.html#traversals

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

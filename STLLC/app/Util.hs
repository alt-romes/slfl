module Util where
    
import Syntax

---- Apply a function to edit certain expression constructors arbitrarily deep in the expression

editexp :: (Expr -> Bool) -> (Expr -> Expr) -> Expr -> Expr
editexp c f e = if c e then f e else editexp' c f e
    where
        editexp' c f (Abs x t e) = Abs x t $ editexp c f e
        editexp' c f (App e1 e2) = App (editexp c f e1) (editexp c f e2)
        editexp' c f (TensorValue e1 e2) = TensorValue (editexp c f e1) (editexp c f e2)
        editexp' c f (LetTensor u v e1 e2) = LetTensor u v (editexp c f e1) (editexp c f e2)
        editexp' c f (LetUnit e1 e2) = LetUnit (editexp c f e1) (editexp c f e2)
        editexp' c f (WithValue e1 e2) = WithValue (editexp c f e1) (editexp c f e2)
        editexp' c f (Fst e) = Fst $ editexp c f e
        editexp' c f (Snd e) = Snd $ editexp c f e
        editexp' c f (InjL t e) = InjL t $ editexp c f e
        editexp' c f (InjR t e) = InjR t $ editexp c f e
        editexp' c f (CaseOfPlus e1 x e2 y e3) = CaseOfPlus (editexp c f e1) x (editexp c f e2) y (editexp c f e3)
        editexp' c f (BangValue e) = BangValue (editexp c f e)
        editexp' c f (LetBang x e1 e2) = LetBang x (editexp c f e1) (editexp c f e2)
        editexp' c f (IfThenElse e1 e2 e3) = IfThenElse (editexp c f e1) (editexp c f e2) (editexp c f e3)
        editexp' c f (LetIn x e1 e2) = LetIn x (editexp c f e1) (editexp c f e2)
        editexp' c f e = e      -- atomic expressions

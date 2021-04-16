module Desugar where

import CoreSyntax
import Syntax
import TypeCheck

desugar :: Expr -> CoreExpr

-- desugar (Var id)

-- desugar (Abs id t e) =
-- desugar (App e1 e2)

desugar (Syntax.TensorValue e1 e2) = CoreSyntax.TensorValue (desugar e1) (desugar e2)
desugar (Syntax.LetTensor i1 i2 e1 e2) = CoreSyntax.LetTensor i1 i2 (desugar e1) (desugar e2)

desugar Syntax.UnitValue = CoreSyntax.UnitValue
desugar (Syntax.LetUnit e1 e2) = CoreSyntax.LetUnit (desugar e1) (desugar e2)

desugar (Syntax.WithValue e1 e2) = CoreSyntax.WithValue (desugar e1) (desugar e2)
desugar (Syntax.Fst e) = CoreSyntax.Fst $ desugar e
desugar (Syntax.Snd e) = CoreSyntax.Snd $ desugar e

desugar (Syntax.InjL t e) = CoreSyntax.InjL t $ desugar e
desugar (Syntax.InjR t e) = CoreSyntax.InjR t $ desugar e
desugar (Syntax.CaseOfPlus ep i1 e1 i2 e2) = CoreSyntax.CaseOfPlus (desugar ep) i1 (desugar e1) i2 (desugar e2)

desugar (Syntax.BangValue e) = CoreSyntax.BangValue $ desugar e
desugar (Syntax.LetBang id e1 e2) = CoreSyntax.LetBang id (desugar e1) (desugar e2)

desugar (Syntax.IfThenElse e1 e2 e3) = CoreSyntax.IfThenElse (desugar e1) (desugar e2) (desugar e3)

desugar Syntax.Tru = CoreSyntax.Tru
desugar Syntax.Fls = CoreSyntax.Fls

desugar (LetIn id e1 e2) =
    let des1 = desugar e1 in
        CoreSyntax.App (desugar $ Syntax.Abs id (typecheck des1) e2) des1

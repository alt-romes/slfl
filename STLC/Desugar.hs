module Desugar where

import CoreSyntax
import Syntax
import TypeCheck

type Ctxt = [(String, Int)]

desugar :: Desugar.Ctxt -> Expr -> CoreExpr

desugar ctxt (Var id) = maybe (FLVar id) BLVar (lookup id ctxt)

desugar ctxt (Syntax.Abs id t e) = CoreSyntax.Abs t (desugar ((id, length ctxt):ctxt) e)
desugar ctxt (Syntax.App e1 e2) = CoreSyntax.App (desugar ctxt e1) (desugar ctxt e2)

desugar ctxt (Syntax.TensorValue e1 e2) = CoreSyntax.TensorValue (desugar ctxt e1) (desugar ctxt e2)
desugar ctxt (Syntax.LetTensor i1 i2 e1 e2) = CoreSyntax.LetTensor i1 i2 (desugar ctxt e1) (desugar ctxt e2)

desugar ctxt Syntax.UnitValue = CoreSyntax.UnitValue
desugar ctxt (Syntax.LetUnit e1 e2) = CoreSyntax.LetUnit (desugar ctxt e1) (desugar ctxt e2)

desugar ctxt (Syntax.WithValue e1 e2) = CoreSyntax.WithValue (desugar ctxt e1) (desugar ctxt e2)
desugar ctxt (Syntax.Fst e) = CoreSyntax.Fst $ desugar ctxt e
desugar ctxt (Syntax.Snd e) = CoreSyntax.Snd $ desugar ctxt e

desugar ctxt (Syntax.InjL t e) = CoreSyntax.InjL t $ desugar ctxt e
desugar ctxt (Syntax.InjR t e) = CoreSyntax.InjR t $ desugar ctxt e
desugar ctxt (Syntax.CaseOfPlus ep i1 e1 i2 e2) = CoreSyntax.CaseOfPlus (desugar ctxt ep) i1 (desugar ctxt e1) i2 (desugar ctxt e2)

desugar ctxt (Syntax.BangValue e) = CoreSyntax.BangValue $ desugar ctxt e
desugar ctxt (Syntax.LetBang id e1 e2) = CoreSyntax.LetBang id (desugar ctxt e1) (desugar ctxt e2)

desugar ctxt (Syntax.IfThenElse e1 e2 e3) = CoreSyntax.IfThenElse (desugar ctxt e1) (desugar ctxt e2) (desugar ctxt e3)

desugar ctxt Syntax.Tru = CoreSyntax.Tru
desugar ctxt Syntax.Fls = CoreSyntax.Fls

desugar ctxt (LetIn id e1 e2) =
    let des1 = desugar ctxt e1 in
        CoreSyntax.App (desugar ctxt $ Syntax.Abs id (typecheck des1) e2) des1

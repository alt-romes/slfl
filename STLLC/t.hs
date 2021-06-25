data Expr = Var Natural | Lambda Expr;

synth traverseExpr :: (Expr -o Natural);

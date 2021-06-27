data Expr = Var Natural | Lambda Expr | App (Expr * Expr);

synth val :: (Expr -o Natural);

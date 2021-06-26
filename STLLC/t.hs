data Expr = Var Bool | Lambda Expr | App (Expr * Expr);

synth red :: (Expr -o Bool);

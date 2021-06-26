data Expr = Var Natural | Lambda Expr;

# App (Expr * Expr)

synth red :: (Expr -o Natural);

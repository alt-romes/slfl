data Expr = Var Natural | Lamb (Expr * Natural);

synth id :: (Expr -o Expr);

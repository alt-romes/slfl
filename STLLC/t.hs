data Expr = Var Natural | Lamb Expr | App (Expr * Expr);

sum :: (Natural -o (Natural -o Natural))
sum a b = sum b a;

synth val :: (Expr -o Natural);

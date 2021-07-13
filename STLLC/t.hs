data List1 a = Nil1 | Cons1 (a * List1 a);

data List2 a = Nil2 | Cons2 (a * List2 a);

synth conv :: (List1 a -o List2 a);

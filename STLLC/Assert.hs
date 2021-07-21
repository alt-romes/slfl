

data List a = Nil | Cons (a * List a);

synth insert :: Int -o List Int -o List Int | assert (insert 0 (Cons (1, Nil))) == (Cons (0, Cons (1, Nil)));

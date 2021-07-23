data List a = Nil | Cons (a * List a);

synth reverse :: List a -o List a -o List a
  | assert
  (reverse (Cons (1, Cons (2, Nil))) Nil) == (Cons (2, Cons (1, Nil)));

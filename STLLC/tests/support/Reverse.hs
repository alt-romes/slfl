













data List a = Nil | Cons (a * List a);

synth reverse :: List a -o List a -o List a
  | assert
  (reverse (Cons (1, Cons (2, Nil))) Nil) == (Cons (2, Cons (1, Nil)));

#reverse l acc =
#    case l of
#        Nil -> acc
#      | Cons x*xs -> reverse xs (Cons (x, acc));


#main = reverse (Cons (1, Cons (2, Cons (3, Cons (4, Nil))))) Nil;

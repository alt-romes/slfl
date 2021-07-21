data List a = Nil | Cons (a * List a);

data Maybe a = Nothing | Just a;

data Bool = True | False;

#length :: List a -o (Int * List a)
#length x = case x of
#             Nil -> (0, Nil)
#           | Cons y ->
#                 let f*g = y in
#                     let i*r = length g in
#                         ((i + 1), Cons (f, r));


synth singleton :: a -o List a;

synth append :: List a -o List a -o List a;

synth map :: (!(a -o b)) -o List a -o List b;

synth foldl :: !(b -o a -o b) -o b -o List a -o b | depth 3;

synth uncons :: List a -o Maybe (a * List a);

synth foldr :: !(a -o b -o b) -o b -o List a -o b;

synth insert :: a -o List a -o List a | choose 1;

synth concat :: List (List a) -o List a;

synth curry :: ((a * b) -o c) -o a -o b -o c;

main = concat (map (! \x -> Cons (x, Cons (42, Nil))) (Cons (1, Cons (2, Cons (3, Nil)))));

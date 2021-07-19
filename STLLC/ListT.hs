data List a = Nil | Cons (a * List a);

data Tree a = Tip | Node (a * List (Tree a));



#synth test :: ((A -o B) -> Tree A -o Tree B);

synth concat :: (List (List Int) -o List Int);

synth concat2 :: (List (List A) -o List A);

# Result w wrong infinite recursion
synth zip :: ((A -o B -o C) -> List A -o List B -o List C);


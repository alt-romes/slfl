# foldr
data List a = Nil | Cons (a * List a);

synth foldr :: ((a -o b -o b) -> b -o List a -o b);

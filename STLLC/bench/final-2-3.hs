# foldl
data List a = Nil | Cons (a * List a);

synth foldl :: (b -o a -o b) -> b -o List a -o b | choose 1;

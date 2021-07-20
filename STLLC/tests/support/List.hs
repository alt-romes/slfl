data List a = Nil | Cons (a * List a);

data Maybe a = Nothing | Just a;



synth na :: (List Int -o List Int);


synth singleton :: (a -o List a);

synth append :: (List a -o List a -o List a);

synth map :: ((!(a -o b)) -o List a -o List b);

synth foldl :: (!(b -o a -o b) -o b -o List a -o b) | choose 1;

synth uncons :: (List a -o Maybe (a * List a));

synth foldr :: (!(a -o b -o b) -o b -o List a -o b);

synth insert :: (a -o List a -o List a)

synth concat :: (List (List a) -o List a);

data List a = Nil | Cons (a * List a);

data Maybe a = Nothing | Just a;

data Bool = True | False;



# can't synth
#synth isEmpty :: (List a -o Bool);
# can't synth -- should it?
# synth zip :: (!(a -o b -o c) -o List a -o List b -o List c)

synth singleton :: (a -o List a);

synth append :: (List a -o List a -o List a);

synth map :: ((!(a -o b)) -o List a -o List b);

synth foldl :: (!(b -o a -o b) -o b -o List a -o b) | choose 1;

synth uncons :: (List a -o Maybe (a * List a));

synth foldr :: (!(a -o b -o b) -o b -o List a -o b);

synth insert :: (a -o List a -o List a)

synth concat :: (List (List a) -o List a);

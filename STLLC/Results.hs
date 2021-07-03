data List a = Nil | Cons (a * List a);

data Maybe a = Nothing | Just a;


synth return :: (a -o Maybe a);

synth empty :: Maybe a;

synth bind :: (Maybe a -o !(a -o Maybe b) -o Maybe b);

synth maybe :: (!b -o !(a -o b) -o Maybe a -o b);


synth singleton :: (a -o List a);

synth concat :: (List a -o List a -o List a);

# This is apparently infinite if everything before it is uncommented
synth map :: ((!(a -o b)) -o List a -o List b);


# This is unbelievably slow with just `return` uncommented (and possibly infinite with `return` and `empty` uncommented)
#synth insert :: (a -o List a -o List a);

synth foldl :: (!(b -o a -o b) -o b -o List a -o b);

synth uncons :: (List a -o Maybe (a * List a));


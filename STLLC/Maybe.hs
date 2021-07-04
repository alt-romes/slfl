data Maybe a = Nothing | Just a;

data List a = Nil | Cons (a * List a);


synth return :: (a -o Maybe a);

synth empty :: Maybe a;

synth bind :: (Maybe a -o !(a -o Maybe b) -o Maybe b);

synth maybe :: (!b -o !(a -o b) -o Maybe a -o b);

# infinite loop if List a = Nil | Cons (a * ! List a);
synth listToMaybe :: (List a -o Maybe a);


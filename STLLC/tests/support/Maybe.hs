data Maybe a = Nothing | Just a;

data List a = Nil | Cons (a * List a);


synth return :: a -o Maybe a;

synth empty :: Maybe a;

synth bind :: Maybe a -o (a -o Maybe b) -> Maybe b;

synth maybe :: b -> (a -o b) -> Maybe a -o b;

synth listToMaybe :: (List a -o Maybe a);

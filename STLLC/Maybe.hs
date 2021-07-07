data Maybe a = Nothing | Just a;

data List a = Nil | Cons (a * List a);


synth return :: (a -> Maybe a);

synth empty :: Maybe a;

synth bind :: (Maybe a -> !(a -> Maybe b) -> Maybe b);

synth maybe :: (!b -> !(a -> b) -> Maybe a -> b);

synth listToMaybe :: (List a -> Maybe a);

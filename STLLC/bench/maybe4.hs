data Maybe a = Nothing | Just a;

data List a = Nil | Cons (a * List a);

# takes very long
synth listToMaybe :: (List a -o Maybe a);

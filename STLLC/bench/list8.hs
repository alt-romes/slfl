data List a = Nil | Cons (a * List a);

data Maybe a = Nothing | Just a;

synth uncons :: (List a -o Maybe (a * List a));

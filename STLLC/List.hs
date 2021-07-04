data List a = Nil | Cons (a * List a);

data Maybe a = Nothing | Just a;



synth singleton :: (a -o List a);

synth concat :: (List a -o List a -o List a);

#synth map :: (((a -o b)) -o List a -o List b);

#synth foldl :: ((b -o a -o b) -o b -o List a -o b);

synth uncons :: (List a -o Maybe (a * List a));

# is wrong, synth is equal to foldl c parametros trocados -- escrever
synth foldr :: ((a -o b -o b) -o b -o List a -o b);

synth insert :: (a -o List a -o List a);

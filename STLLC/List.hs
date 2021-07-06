data List a = Nil | Cons (a * List a);

data Maybe a = Nothing | Just a;



#synth na :: (List Int -> List Int);


#synth singleton :: (a -> List a);

#synth append :: (List a -> List a -> List a);

#synth map :: ((!(a -> b)) -> List a -> List b);

#synth foldl :: (!(b -> a -> b) -> b -> List a -> b);

#synth uncons :: (List a -> Maybe (a * List a));

# is wrong, synth is equal to foldl c parametros trocados -- escrever
#synth foldr :: (!(a -> b -> b) -> b -> List a -> b);

#synth insert :: (a -> List a -> List a);

synth concat :: (List (List a) -> List a);

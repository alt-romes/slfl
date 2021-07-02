data List a = Nil | Cons (a * List a);


# synth singleton :: (a -o List a);

synth concat :: (List a -o List a -o List a);

synth map :: ((!(a -o b)) -o List a -o List b);



# synth insert :: (!a -o List a -o List a); wrong

# synth foldl :: (!(b -o a -o b) -o b -o List a -o b); loop


data List a = Nil | Cons (a * List a);


synth insert :: (a -o List a);

synth concat :: (List a -o List a -o List a);

synth map :: ((! (a -o b)) -o List a -o List b);

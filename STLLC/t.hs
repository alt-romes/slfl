data List a = Nil | Cons (a * List a);


# infinite loop
synth insert :: (a -o List a);

synth map :: ((! (A -o B)) -o List A -o List B);

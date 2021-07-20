data List a = Nil | Cons (a * List a);

# infinite loop
synth concat :: (List (List a) -o List a);

# concat
data List a = Nil | Cons (a * List a);

synth concat :: List (List a) -o List a;

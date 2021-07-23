# append
data List a = Nil | Cons (a * List a);

synth append :: List a -o List a -o List a;

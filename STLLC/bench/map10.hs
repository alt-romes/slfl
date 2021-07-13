data Map a b = Tip | Bin (a * b * (Map a b) * (Map a b));
data List a = Nil | Cons (a * List a);

# doesn't work
#synth union :: (Map b a -o Map b a -o Map b a);

#synth assocs :: (Map b a -o List (b * a));

data ListBool = Nil | Cons (Nat * ListBool);

data ListNat = Nil | Cons (Nat * ListNat);

synth map :: (ListBool -o ListNat);

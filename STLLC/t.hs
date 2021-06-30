data ListBool = Nil | Cons (Bool * ListBool);

data ListNat = Nil | Cons (Nat * ListNat);

synth map :: ((! (Bool -o Nat)) -o ListBool -o ListNat);

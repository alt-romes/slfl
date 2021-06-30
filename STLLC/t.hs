data ListNatNat = Nil | Cons ((Nat * Nat) * ListNatNat);

data ListNat = Nil | Cons (Nat * ListNat);

synth map :: (ListNatNat -o ListNat);

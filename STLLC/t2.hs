data Con = Con Nat;

sum :: (Nat -o (Nat -o Nat));
sum a b = sum b a;

synth val :: (Con -o (Con -o Nat));

data Con = Con Nat;

sum :: (Nat -o (Nat -o Nat));
sum a b = sum b a;

val :: (Con -o (Con -o Nat));
val a b = case b of 
      Con c -> 
        case a of 
              Con d -> val (Con c) (Con d);

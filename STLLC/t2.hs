data Maybe a = Nothing | Just a;


#synth return :: (Nat -o Maybe Nat);
synth bind :: (Maybe Nat -o ! (Nat -o Maybe Bool) -o Maybe Bool)

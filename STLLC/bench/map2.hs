data Map a b = Tip | Bin (a * b * (Map a b) * (Map a b));

synth singleton :: (a -o b -o Map a b);

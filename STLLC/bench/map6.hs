data Map a b = Tip | Bin (a * b * (Map a b) * (Map a b));

synth union :: (Map a b -o Map a b -o Map a b);

data Map a b = Tip | Bin (a * b * (Map a b) * (Map a b));

synth insertWithKey :: ((a -o b -o b -o b) -> a -o b -o Map a b -o Map a b);

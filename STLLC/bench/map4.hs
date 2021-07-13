data Map a b = Tip | Bin (a * b * (Map a b) * (Map a b));

synth insertWith :: ((b -o b -o b) -> a -o b -o Map a b -o Map a b);

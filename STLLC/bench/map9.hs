data Map a b = Tip | Bin (a * b * (Map a b) * (Map a b));

synth mapKeys :: ((a -o b) -> Map a c -o Map b c);

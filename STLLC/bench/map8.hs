data Map a b = Tip | Bin (a * b * (Map a b) * (Map a b));

synth map :: ((a -o b) -> Map d a -o Map d b)

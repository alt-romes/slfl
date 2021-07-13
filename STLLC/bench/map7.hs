data Map a b = Tip | Bin (a * b * (Map a b) * (Map a b));

# Fails
synth mapAccum :: ((a -o b -o (a * c)) -> a -o Map d b -o (a * Map d c));

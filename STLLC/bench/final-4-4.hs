# get
data State b a = State (!b -o (a * !b));

synth get :: State a a;

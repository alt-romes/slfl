# put
data State b a = State (!b -o (a * !b));

synth put :: !a -o (State a 1);

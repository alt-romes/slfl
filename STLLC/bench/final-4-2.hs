# >>=
data State b a = State (!b -o (a * !b));

synth bind :: State c a -o (a -o State c b) -o State c b;

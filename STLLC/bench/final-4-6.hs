# modify
data State b a = State (!b -o (a * !b));

synth modify :: (!a -o !a) -o State a 1;

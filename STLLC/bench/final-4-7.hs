# evalState
data State b a = State (!b -o (a * !b));

synth evalState :: State b a -o !b -o a;

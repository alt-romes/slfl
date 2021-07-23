# runState
data State b a = State (!b -o (a * !b));

synth runState :: State b a -o (!b -o (a * !b));

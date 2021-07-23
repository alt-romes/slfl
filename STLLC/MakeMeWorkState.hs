data State b a = State (!b -o (a * !b));

synth runState :: State b a -o (!b -o (a * !b));

synth bind :: State c a -o (a -o State c b) -o State c b;

#synth bind :: (State c a -o (a -o State c b) -o State c b) | using (runState);

synth return :: a -o State b a;

synth get :: State a a;

synth put :: !a -o (State a 1);

synth modify :: (!a -o !a) -o State a 1;

synth evalState :: State b a -o !b -o a;


main = runState (bind (return 2) (\x -> return x)) (!0);

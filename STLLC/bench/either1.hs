data Either a b = Left a | Right b;

synth either :: ((a -o c) -> (b -o c) -> Either a b -o c);

data List a = Nil | Cons (a * List a);
data Either a b = Left a | Right b;

synth partitionEithers :: ((a -o c) -> (b -o c) -> Either a b -o c);

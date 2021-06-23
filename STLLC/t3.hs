

curry :: forall a b c . (((a * b) -o c) -o (a -o (b -o c)));
curry a b = (λc -o a ( b , c ));

uncurry :: forall a b c . ((a -o (b -o c)) -o ((a * b) -o c));
uncurry a b = let c*d = b in a c d;



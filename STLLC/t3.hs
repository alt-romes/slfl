

curry :: forall a b c . (((a * b) -o c) -o (a -o (b -o c)));
curry = {{ (((a * b) -o c) -o (a -o (b -o c))) }};

uncurry :: forall a b c . ((a -o (b -o c)) -o ((a * b) -o c));
uncurry = {{ ((a -o (b -o c)) -o ((a * b) -o c)) }};



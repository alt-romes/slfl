data Maybe a = Nothing | Just a;


# synth return :: (a -o Maybe a);


synth bind :: (Maybe a -o (a -o Maybe b) -o Maybe b);


#synth maybe :: (!b -o !(a -o b) -o Maybe a -o b);

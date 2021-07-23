# maybe
data Maybe a = Nothing | Just a;

synth maybe :: b -> (a -o b) -> Maybe a -o b;

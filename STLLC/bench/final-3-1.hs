# >>=
data Maybe a = Nothing | Just a;

synth bind :: Maybe a -o (a -o Maybe b) -> Maybe b;

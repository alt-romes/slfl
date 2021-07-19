#-- main :: forall a b c d . ((! (a -o b)) -o (((! (a -o b)) -o (d -o c)) -o (d -o c)));
main e f g = let !h = e in f (!(λk -> h k)) g;

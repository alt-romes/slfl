data Maybe a = Nothing | Just a;

data List a = Nil | Cons (a * List a);


return :: forall a . (a -o Maybe a);
return b = Just b;

empty :: forall a . Maybe a;
empty = Nothing;

bind :: forall a b . (Maybe a -o ((! (a -o Maybe b)) -o Maybe b));
bind c d = let !e = d in
    case c of
          Nothing  -> Nothing
        | Just f -> e f;

maybe :: forall a b . ((! b) -o ((! (a -o b)) -o (Maybe a -o b)));
maybe c d e = case e of
      Nothing  ->
        let !f = d in
            let !g = c in g
    | Just h ->
        let !i = d in
            let !j = c in i h;

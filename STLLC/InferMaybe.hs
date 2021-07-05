data Maybe a = Nothing | Just a;

data List a = Nil | Cons (a * List a);


return :: forall a . (a -> Maybe a);
return = Just;

empty :: forall a . Maybe a;
empty = Nothing;

bind :: forall a b . (Maybe a -> (!(a -> Maybe b) -> Maybe b));
bind c d = let !e = d in 
    case c of 
          Nothing  -> Nothing
        | Just f -> e f;

maybe :: forall a b . (!b -> (!(a -> b) -> (Maybe a -> b)));
maybe c d e = case e of 
      Nothing  -> 
        let !f = d in 
            let !g = c in g
    | Just h -> 
        let !i = d in 
            let !j = c in i h;



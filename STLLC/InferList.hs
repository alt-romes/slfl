data List a = Nil | Cons (a * List a);

data Maybe a = Nothing | Just a;


singleton :: forall a . (a -o List a);
singleton b = Cons ( b , Nil );

append :: forall a . (List a -o (List a -o List a));
append b c = case c of 
      Nil  -> b
    | Cons d -> 
        let e*f = d in Cons ( e , append f b );

map :: forall a b . ((! (a -o b)) -o (List a -o List b));
map c d = case d of 
      Nil  -> 
        let !e = c in Nil
    | Cons f -> 
        let g*h = f in 
            let !i = c in Cons ( i g , map (! (λo -o i o)) h );

foldl :: forall a b . ((! (b -o (a -o b))) -o (b -o (List a -o b)));
foldl c d e = case e of 
      Nil  -> 
        let !f = c in d
    | Cons g -> 
        let h*i = g in 
            let !j = c in j (foldl (!j) d i) h;

uncons :: forall a . (List a -o Maybe (a * List a));
uncons b = case b of 
      Nil  -> Nothing
    | Cons c -> 
        let d*e = c in Just ( d , e );

foldr :: forall a b . ((! (a -o (b -o b))) -o (b -o (List a -o b)));
foldr c d e = case e of 
      Nil  -> 
        let !f = c in d
    | Cons g -> 
        let h*i = g in 
            let !j = c in j h (foldr ! (λr -o (λs -o j r s)) d i);

insert :: forall a . (a -o (List a -o List a));
insert b c = case c of 
      Nil  -> Cons ( b , Nil )
    | Cons p -> 
        let q*r = p in Cons ( b , Cons ( q , r ) );



data List a = Nil | Cons (a * List a);

data Tree a = Node (a * List (Tree a));

#synth map :: ((a -o b) -> List a -o List b);

#unfoldTree f b = let !fx = f in
#    let a*bs = fx b in Node (a, (map (unfoldTree fx) bs));

#synth unfoldTree :: ((b -o (a * List b)) -> b -o Tree a) | using (map unfoldTree) | depth 5;

synth insert :: (a -o Tree a -o Tree a);

synth return :: (a -o Tree a);


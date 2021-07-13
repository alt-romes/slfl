
data List a = Nil | Cons (a * List a);

data Tree a = Leaf | Node (a * List (Tree a));


synth insert :: (a -o Tree a -o Tree a);

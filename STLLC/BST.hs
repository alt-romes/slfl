data Bool = True | False;

data BST a = Empty | Node (a * BST a * BST a);

size :: BST a -o (Int * BST a);
size b = case b of
    Empty -> (0, Empty)
  | Node d*e*f -> 
      let s1*t1 = size e in
          let s2*t2 = size f in
            (1 + s1 + s2, Node ((d, t1), t2));


synth singleton :: (a -o BST a);

synth insert :: (!a -o BST a -o BST a);

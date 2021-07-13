data BinTree a = Nil | Node (a * BinTree a * BinTree a);

synth root :: (a -o BinTree a -o BinTree a -o BinTree a);

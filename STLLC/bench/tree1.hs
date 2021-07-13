data BinTree a = Nil | Node (a * BinTree a * BinTree a);

synth singleton :: (a -o BinTree a);

data BinTree a = Nil | Node (a * BinTree a * BinTree a);

synth map :: ((a -o b) -> BinTree a -o BinTree b);

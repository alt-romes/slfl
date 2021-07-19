data BST a = Nil | Node (a * BST a * BST a); 

data Maybe a = Nothing | Just a;

synth return :: (a -o BST a);

synth insert :: (a -o BST a -o BST a);

synth id :: (BST a -o BST a);

synth map :: ((a -o b) -> BST a -o BST b);

synth uncons :: (BST a -o Maybe (a * (BST a) * (BST a)));

# fails after a long time
#synth foldl :: ((b -o a -o b) -> b -o BST a -o b);

data List a = Nil | Cons (a * List a);

newMArray :: (Int -> (MArray a -o !b) -o b);

write :: (MArray a -o (Int * a) -> MArray a);

freeze :: (MArray a -o !(Array a));

foldl :: ((a -o b -o a) -> a -o (List b) -o a)

synth array :: (Int -> List (Int * a) -> Array a);

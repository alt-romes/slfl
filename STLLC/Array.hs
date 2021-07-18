
foldl :: ((a -o b -o a) -> a -o (List b) -o a);

newMArray :: (Int -> (MArray a -o !b) -o b);

write :: (MArray a -o (Int * a) -> MArray a);

#read :: (MArray a -o Int -> (MArray a * !a));

freeze :: (MArray a -o !(Array a));

synth array :: (Int -> List (!(Int * a)) -> Array a)
  | using (foldl) | depth 3;

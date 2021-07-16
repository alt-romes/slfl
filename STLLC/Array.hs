
data List a = Nil | Cons (a * List a);


newMArray :: (Int -o (MArray a -o !b) -o b);

write :: (MArray a -o (Int * a) -o MArray a);

freeze :: (MArray a -o !(Array a));

foldl :: ((a -o b -o a) -> a -o (List b) -o a)

synth array :: (Int -o List (Int * a) -o Array a);

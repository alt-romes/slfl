
synth plus :: (x {Int} -> y {Int} -> z { Int | z == x + y });

synth inc :: (x {Int} -> y { Int | y == x + 1 });

synth deq :: (x {Int} -> y { Int | y == x - 1 });

synth mm :: (x {Int} -> y {Int} -> z {Int} -> k { Int | k == x - y + z });

synth plus20 :: (x { Int | x > 0 } -> y { Int | y == x + 20 });

synth number :: (x { Int | x > 345 && x != 346 })

# comment me
synth impossible :: (x {Int} -> y {Int} -> z {Int} -> k { Int | k == x * y + z });

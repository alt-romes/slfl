
synth plus :: (x {Int} -o y {Int} -o z { Int | z == x + y });

synth inc :: (x {Int} -o y { Int | y == x + 1 });

synth deq :: (x {Int} -o y { Int | y == x - 1 });

# is this correct?
synth mm :: (x {Int} -o y {Int} -o z {Int} -o k { Int | k == x - y + z });

synth plus20 :: (x { Int | x > 0 } -o y { Int | y == x + 20 });

synth number :: (x { Int | x > 345 && x != 346 });

# correct me
synth add3 :: (x {Int} -o y {Int} -o z {Int} -o k {Int | k == x + y + z});

# comment me
#synth impossible :: (x {Int} -o y {Int} -o z {Int} -o k { Int | k == x * y + z });

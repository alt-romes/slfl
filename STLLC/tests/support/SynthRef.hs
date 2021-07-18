

# Right Focus Synth

synth plus :: (x {Int} -o y {Int} -o z { Int | z == x + y });

synth inc :: (x {Int} -o y { Int | y == x + 1 });

synth deq :: (x {Int} -o y { Int | y == x - 1 });

# is this correct?
synth mm :: (x {Int} -o y {Int} -o z {Int} -o k { Int | k == x - y + z });

synth plus20 :: (x { Int | x > 0 } -o y { Int | y == x + 20 });

synth number :: (x { Int | x > 345 && x != 346 });

# correct me
synth add3 :: (x {Int} -o y {Int} -o z {Int} -o k {Int | k == x + y + z});

synth fn :: (x {Int} -o y {Int} -o z {Int} -o k {Int | x + k == y * z});

# comment me
#synth impossible :: (x {Int} -o y {Int} -o z {Int} -o k { Int | k == x * y + z });


# Left Focus Synth

# how to avoid stupid functions so that add is attempted
#synth s :: (x {Int | x > 5} -o y {Int | y > x} -o z {Int});


synth inc :: (x {Int} -o y {Int | y == x + 1});

synth shouldntfail :: (x {Int} -o y {Int | y > x});

synth addplus1 :: (x {Int} -o y {Int} -o z {Int | z == x + y + 1});

synth shouldntfail2 :: (x {Int | x > 0} -o y {Int | y > 0} -o z {Int | z > x + y});

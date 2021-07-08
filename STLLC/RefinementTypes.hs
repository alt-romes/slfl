
# Refinements work: can you make this program typecheck? :)

nat :: x { Int | x > 0 };
nat = add 6 3;

sum2 = add 6 3;


wplus :: (x { Int } -> y { Int | x == y } -> z { Int | z >= x + y });
wplus x y = add x y;


inc :: (x { Int | x >= 0 } -> z { Int | z == x + 1 && x == 0 });
inc = add 1;


pluswrong :: (x { Int } -> y { Int } -> z { Int | z == x + y });
pluswrong x y = add x y;


j :: (x {Int | x == 1 } -> y { Int | y == x && y >= 1 })
j x = x


# Refinements work: can you make this program typecheck? :)

nat :: x { Int | x < 0 };
nat = add 6 3;


wplus :: (x { Int } -> y { Int | x > y } -> z { Int | z == x + x });
wplus x y = add x y;


inc :: (x { Int | x > 0 } -> z { Int | z == x + 2 });
inc = add 1;


pluswrong :: (x { Int } -> y { Int } -> z { Int | z > x + y });
pluswrong x y = add x y;

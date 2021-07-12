
nat :: x { Int | x > 0 };
nat = add 6 3;

sum2 = add 6 3;

sum3 = add 3;

wplus :: (x { Int } -o y { Int | x == y } -o z { Int | z >= x + y });
wplus x y = add x y;


inc :: (x { Int | x >= 0 } -o z { Int | z == x + 1 && x == 0 });
inc = add 1;


pluswrong :: (x { Int } -o y { Int } -o z { Int | z == x + y });
pluswrong x y = add x y;


j :: (x {Int | x == 1 } -o y { Int | y == x && y >= 1 });
j x = x;

test :: (x {Int} -o y {Int} -o z {Int | z > x + y && z < x - y});
test = test

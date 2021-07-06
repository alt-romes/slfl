

# radd = add;

# rsub = sub;

# rmult = mult 4;

# num :: x { Int | x > 0 }
#num = 3;






#nat :: x { Int | x > 0 };
#nat = add 6 3;






#plus :: (x { Int } -> y { Int } -> z { Int | z < x + y });
#plus x y = add x y;

inc :: (x { Int | x > 0 } -> z { Int | z == x + 1 });
inc x = add x 2;

#pluswrong :: (x { Int } -> y { Int | y == x } -> z { Int | z > x + y });
#pluswrong x y = add x y;

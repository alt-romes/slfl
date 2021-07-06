

# radd = add;

#rsub = sub;

#rmult = mult 4;

num :: x { Int | x > 0 }
num = 3;

#     smtSat (x > 0) 
#  ------------------ (ENT-Emp??? ent e o ctxt?)
#   x: Int |- x > 0
# ----------------------- (WF-Base)
#nat :: x { Int | x > 0 };
#nat = add 6 3;

#                               x:Int, y:Int |- true            X:Int, y:Int, z:Int |- z == x + y
#                              ----------------------         ----------------------------------------------- (WF-BASE?)
#   x: Int |- true             x { Int } |- y { Int }          x { Int }, y { Int } |- z { Int | z == x + y }         
#  -----------------          ------------------------------------------------------------- (WF-Fun)
#    ø |- x { Int }             x { Int } |- y { Int } -> z { Int | z == x + y}
# ------------------------------------------------------------------------------- (WF-Fun)
plus :: (x { Int } -> y { Int } -> z { Int | z == x + y });
plus x y = add x y;

#                                 x: Int, z: Int |- x > 0 => z == x + 1
#   ------------------(SMT)     ---------------------------------------------
#    x: Int |- x > 0              x { Int | x > 0 }, z : Int |- z == x + 1
#   -----------------           -------------------------------------------
#   x { Int | x > 0 }           x { Int | x > 0 } |- z { Int | z == x + 1 }
# ---------------------------------------------------------------------------
inc :: (x { Int | x > 0 } -> z { Int | z == x + 1 });
inc x = add x 1;


pluswrong :: (x { Int } -> y { Int | y == x } -> z { Int | z > x + y });
pluswrong x y = add x y;

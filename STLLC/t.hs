data Num = Zero | Succ Num;

let main x = case x of
               Zero => 0
               | Succ x => main x;

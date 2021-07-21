data Bool = False | True;

t = 2;

main = case (4 + 3 + t == t + 7) => 4 < t of
         True -> 0 - 1
        | False -> 0 - 2;

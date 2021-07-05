nat = \x : x { Nat | x > 0 } -o x;

plus = \x : (x { Nat } -o y { Nat } -o z { Nat | z == x + y } ) -o x;

inc = \x : (x { Nat } -o z { Nat | z == x + 1 } ) -o x;

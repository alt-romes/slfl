data List a = Nil | Cons (a * List a);


# infinite loop
# synth insert :: (a -o List a);

# infinite loop
synth insert :: (Nat -o List Nat);

# infinite loop
# synth map :: ((! (a -o b)) -o List a -o List b);

# working
#synth map :: ((! (Foo -o Bar)) -o List Foo -o List Bar);

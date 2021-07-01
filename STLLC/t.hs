data List a = Nil | Cons (a * List a);


# synth insert :: (a -o List a); -- infinite

# synth map :: ((! (a -o b)) -o List a -o List b) -- wrong

# wrong -- it seems like the "type of the list" isn't being taken into consideration
synth map :: ((! (Nat -o Bool)) -o List Nat -o List Bool);


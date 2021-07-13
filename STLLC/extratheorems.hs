
#https://arxiv.org/pdf/1904.06850v1.pdf

# multiplicative translation
synth f0 :: ((A -o B) -o (B -o C) -o (A -o C));

# call by name
synth f1 :: (!(!A -o B) -o !(!B -o C) -o (!A -o C));

# call by value
synth f2 :: (!(!A -o !B) -o !(!B -o !C) -o !(!A -o !C));

# 0 / 1
synth f3 :: (!(!A -o !B) -o !(!B -o !C) -o !(!A -o C));


# vectors

synth f4 :: (!(A -o B) -o (A * A * A * A) -o (B * B * B * B));

# pull?

synth f5 :: ((!A + !B) -o !(A + B));

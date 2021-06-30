data Bool = True | False;
data List a = Nil | Cons (a * List a);

right = Cons (1, Cons (2, Cons (3,Nil)));

# delete this
wrong = Cons (1, Cons (True, Nil));

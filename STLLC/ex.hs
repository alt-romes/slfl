data Expr = Var Natural | Lambda Expr | App (Expr * Expr);

data List = Nil | Cons (Natural * List);


# -- wrong - shouldn't use constructor
# -- restrict constructor & deconstruct
value :: (Expr -o Natural);
value a = case a of 
      Var b -> b
    | Lambda c -> value c
    | App e -> value 
        let i*j = e in App ( Var (value i) , Var (value j) );

# -- right -- should use constructor
# -- restrict deconstruct
expr :: (Expr -o Expr);
expr a = case a of 
      Var b -> Var b
    | Lambda c -> c
    | App d -> 
        let e*f = d in App ( Var (value e) , Var (value f) );

# -- right -- should use constructor
# -- no restrict
insert :: (Natural -o List);
insert a = Cons ( a , Nil );

# -- wrong -- should not use constructor at all, maybe it shouldn't even work -- isn't it a partial function ?
# -- restrict constructor & deconstruct
head :: (List -o Natural);
head a = case a of 
      Nil  -> head Nil
    | Cons c -> head 
        let g*h = c in Cons ( g , Cons ( head h , Nil ) );

# -- correct -- should use constructor
# -- restrict deconstruct
list :: (List -o List);
list a = case a of 
      Nil  -> Nil
    | Cons b -> 
        let c*d = b in Cons ( c , Cons ( head d , Nil ) );

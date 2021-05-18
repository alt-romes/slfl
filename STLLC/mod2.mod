(λx: (A -o (B -o C)) ->
    (λy : (A * B) ->
        let z*u = y in
            let v = x z in v u));

let b = (λx : ((A * B) -o C) ->
    (λy : A ->
        (λz : B -> x <y * z>)));

let c = (λx : (A -o (B & C)) -> <
    (λy : A ->
        let z = x y in fst z) &
    (λv : A ->
        let a = x v in snd a)>);

let d = (λx : ((A -o B) & (A -o C)) ->
    (λy : A -> <
        let z = fst x in z y &
        let b = snd x in b y>));

let e = (λx : ((A + B) -o C) -> <
    (λy : A -> x inl (y) : B) &
    (λu : B -> x inr A : (u))>);

let f = (λx : ((A -o C) & (B -o C)) ->
    (λy : (A + B) ->
        case y of
            inl z =>
                let v = fst x in v z
            | inr u =>
                let d = snd x in d u));

let g = (λx : (! (A & B)) ->
    let !y = x in < !fst y * !snd y >);

let h = (λx : ((! A) * (! B)) ->
    let y*z = x in
        let !u = z in
            let !v = y in ! <v & u>);

let i = (λx : (A * 1) ->
    let y*z = x in
        let _ = z in y);

let j = (λx : A -> <x * <>>);

let k = (λx : (A & A) -> fst x);

let l = (λx : A -> <x & x>);

a

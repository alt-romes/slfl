module LinearSequentCheck where

import CoreSyntax

type Index = Int
type Name = String

type BoundCtxt = [(Index, Type)]
type FreeCtxt = [(Name, Type)]
type Ctxt = (BoundCtxt, FreeCtxt)


-- lincheck --- Depth, Gamma, DeltaIn, Expr -> (Type, DeltaOut)

lincheck :: Int -> Ctxt -> Ctxt -> CoreExpr -> Maybe (Type, Ctxt)

--- hyp --------------------

lincheck depth gam (bdel, fdel) (BLVar x) = do
    let (maybet, bdel') = findDelete x bdel []
    t <- maybet
    return (t, (bdel', fdel))

lincheck depth gam (bdel, fdel) (FLVar x) = do
    let (maybet, fdel') = findDelete x fdel []
    t <- maybet
    return (t, (bdel, fdel'))

lincheck depth (bgam, fgam) del (BUVar x) = do
    t <- lookup x bgam
    return (t, del)

lincheck depth (bgam, fgam) del (FUVar x) = do
    t <- lookup x fgam
    return (t, del)

--- -o ---------------------

--  -oI
lincheck depth gam (bdel, fdel) (Abs t1 e) = do
    (t2, del2) <- lincheck (depth+1) gam ((depth, t1):bdel, fdel) e
    return (Fun t1 t2, del2)

--  -oE
lincheck depth gam del (App e1 e2) = do
    (Fun t1 t2, del1) <- lincheck depth gam del e1
    (t, del2) <- lincheck depth gam del1 e2
    if t == t1 then return (t2, del2)
    else Nothing

--- * ----------------------

--  *I
lincheck depth gam del (TensorValue e1 e2) = do
    (t1, del2) <- lincheck depth gam del e1
    (t2, del3) <- lincheck depth gam del2 e2
    return (Tensor t1 t2, del3)

--  *E
lincheck depth gam del (LetTensor e1 e2) = do
    (Tensor t1 t2, (bdel', fdel')) <- lincheck depth gam del e1
    (t3, del3) <- lincheck (depth+2) gam ((depth, t1):((depth+1, t2):bdel'), fdel') e2
    return (t3, del3)

--- 1 ----------------------

--  1I
lincheck depth gam del UnitValue = return (Unit, del)

--  1E
lincheck depth gam del (LetUnit e1 e2) = do
    (Unit, del2) <- lincheck depth gam del e1
    (t2, del3) <- lincheck depth gam del2 e2
    return (t2, del3)

--- & ----------------------

--  &I
lincheck depth gam del (WithValue e1 e2) = do
    (t1, del2) <- lincheck depth gam del e1
    (t2, del3) <- lincheck depth gam del e2
    if del2 == del3 then return (With t1 t2, del2)
    else Nothing

--  &E
lincheck depth gam del (Fst e) = do
    (With t1 t2, del2) <- lincheck depth gam del e
    return (t1, del2)

--  &E
lincheck depth gam del (Snd e) = do
    (With t1 t2, del2) <- lincheck depth gam del e
    return (t2, del2)

--- + ----------------------

--  +I
lincheck depth gam del (InjL t1 e) = do
    (t2, del2) <- lincheck depth gam del e
    return (Plus t2 t1, del2)

--  +I
lincheck depth gam del (InjR t1 e) = do
    (t2, del2) <- lincheck depth gam del e
    return (Plus t1 t2, del2)

--  +E
lincheck depth gam del (CaseOfPlus e1 e2 e3) = do
    (Plus t1 t2, (bdel', fdel')) <- lincheck depth gam del e1
    (t3, del3) <- lincheck (depth+1) gam ((depth, t1):bdel', fdel') e2
    (t4, del4) <- lincheck (depth+1) gam ((depth, t2):bdel', fdel') e3
    if t3 == t4 && del3 == del4
       then return (t4, del4)
       else Nothing

--- ! ----------------------

--  !I
lincheck depth gam del (BangValue e) = do
    (t2, del2) <- lincheck depth gam del e
    if del2 /= del then Nothing
    else return (Bang t2, del)

--  !E
lincheck depth (bgam, fgam) del (LetBang e1 e2) = do
    (Bang t1, del2) <- lincheck depth (bgam, fgam) del e1
    lincheck (depth+1) ((depth, t1):bgam, fgam) del2 e2


--- ? ----------------------

-- Onde é que estas regras se enquadram? Como é que lhes chamamos?
lincheck depth gam del Tru = return (Bool, del)
lincheck depth gam del Fls = return (Bool, del)

lincheck depth gam del (IfThenElse e1 e2 e3) = do
    (Bool, del1) <- lincheck depth gam del e1
    (t2, del2) <- lincheck depth gam del1 e2
    (t3, del3) <- lincheck depth gam del1 e2
    if t2 == t3 && del2 == del3
       then return (t3, del3)
       else Nothing

-- end lincheck ------------



-- util --------------------

findDelete :: (Eq a) => a -> [(a, b)] -> [(a, b)] -> (Maybe b, [(a, b)])
findDelete _ [] _ = (Nothing, [])
findDelete x ((y,t):xs) acc =
    if x==y then (Just t, reverse acc ++ xs)
    else findDelete x xs ((y,t):acc)

-- top level ---------------

typecheck :: CoreExpr -> Type
typecheck e = maybe (error "typecheck") fst (lincheck 0 ([], []) ([], []) e)

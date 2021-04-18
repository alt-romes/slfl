module LinearSequentCheck where

import CoreSyntax

type Index = Int
type Name = String

type BoundCtxt = [(Index, Type)]
type FreeCtxt = [(Name, Type)]
type Ctxt = (BoundCtxt, FreeCtxt)

--              Gamma, DeltaIn, Expr -> (Type, DeltaOut)
sequentcheck :: Int -> Ctxt -> Ctxt -> CoreExpr -> Maybe (Type, Ctxt)

-- hyptothesis
sequentcheck depth gam (bdel, fdel) (BLVar x) = do
    let (maybet, bdel') = findDelete x bdel []
    t <- maybet
    return (t, (bdel', fdel))

sequentcheck depth gam (bdel, fdel) (FLVar x) = do
    let (maybet, fdel') = findDelete x fdel []
    t <- maybet
    return (t, (bdel, fdel'))

-- sequentcheck depth (bgam, fgam) del (BUVar x) = do
--     let (maybet, fdel') = findDelete x fdel []
--     t <- maybet
--     return (t, (bdel, fdel'))


--  -oR
sequentcheck depth gam (bdel, fdel) (Abs t1 e) = do
    (t2, del2) <- sequentcheck (depth+1) gam ((depth, t1):bdel, fdel) e
    return (Fun t1 t2, del2)

--  -oL
sequentcheck depth gam del (App e1 e2) = 



--  *R
sequentcheck depth gam del (TensorValue e1 e2) = do
    (t1, del2) <- sequentcheck depth gam del e1
    (t2, del3) <- sequentcheck depth gam del2 e2
    return (Tensor t1 t2, del3)

--  1R
sequentcheck depth gam del UnitValue = return (Unit, del)

--  &R
sequentcheck depth gam del (WithValue e1 e2) = do
    (t1, _) <- sequentcheck depth gam del e1
    (t2, del2) <- sequentcheck depth gam del e2 -- double check delta I/O
    return (With t1 t2, del2)

--  +R
sequentcheck depth gam del (InjL t1 e) = do
    (t2, del2) <- sequentcheck depth gam del e
    return (Plus t2 t1, del2)

--  +R
sequentcheck depth gam del (InjR t1 e) = do
    (t2, del2) <- sequentcheck depth gam del e
    return (Plus t1 t2, del2)

--  !R
sequentcheck depth gam del (BangValue e) = do
    (t2, del2) <- sequentcheck depth gam del e
    if del2 /= del then Nothing
    else return (Bang t2, del)

-- Onde é que estas regras se enquadram? Como é que lhes chamamos?
sequentcheck depth gam del Tru = return (Bool, del)
sequentcheck depth gam del Fls = return (Bool, del)


-- focuscheck :: Ctxt -> Ctxt -> Ctxt -> Bool -> CoreExpr -> Maybe (Type, Ctxt, Ctxt, Ctxt)

-- focuscheck cgam cdel comg (TensorValue e1 e2) True = Nothing


-- util

findDelete :: (Eq a) => a -> [(a, b)] -> [(a, b)] -> (Maybe b, [(a, b)])
findDelete _ [] _ = (Nothing, [])
findDelete x ((y,t):xs) acc =
    if x==y then (Just t, reverse acc ++ xs)
    else findDelete x xs ((y,t):acc)

-- top level

typecheck :: CoreExpr -> Type
typecheck e = maybe (error "typecheck") fst (sequentcheck 0 ([], []) ([], []) e)

module LinearSequentCheck where

import CoreSyntax

type Ctxt = ([Type], [(String, Type)])

--              Gamma, DeltaIn, Expr -> (Type, DeltaOut)
sequentcheck :: Ctxt -> Ctxt -> CoreExpr -> Maybe (Type, Ctxt)

--  -oR
sequentcheck gam (bdel, fdel) (Abs t1 e) = do
    (t2, del2) <- sequentcheck gam (t1:bdel, fdel) e
    return (Fun t1 t2, del2)

--  *R
sequentcheck gam del (TensorValue e1 e2) = do
    (t1, del2) <- sequentcheck gam del e1
    (t2, del3) <- sequentcheck gam del2 e2
    return (Tensor t1 t2, del3)

--  1R
sequentcheck gam del UnitValue = return (Unit, del)

--  &R
sequentcheck gam del (WithValue e1 e2) = do
    (t1, _) <- sequentcheck gam del e1
    (t2, del2) <- sequentcheck gam del e2
    return (With t1 t2, del2)

--  +R
sequentcheck gam del (InjL t1 e) = do
    (t2, del2) <- sequentcheck gam del e
    return (Plus t2 t1, del2)

--  +R
sequentcheck gam del (InjR t1 e) = do
    (t2, del2) <- sequentcheck gam del e
    return (Plus t1 t2, del2)

--  !R
sequentcheck gam del (BangValue e) = do
    (t2, del2) <- sequentcheck gam del e
    if del2 /= del then Nothing
    else return (Bang t2, del)

-- --  -oL
-- sequentcheck gam (bdel, fdel) (App e1 e2) = do
--     (t2, gam2, del2) <- sequentcheck gam (t1:bdel, fdel) e
--     return (Fun t1 t2, gam2, del2)

sequentcheck gam del Tru = return (Bool, del)
sequentcheck gam del Fls = return (Bool, del)



-- focuscheck :: Ctxt -> Ctxt -> Ctxt -> Bool -> CoreExpr -> Maybe (Type, Ctxt, Ctxt, Ctxt)

-- focuscheck cgam cdel comg (TensorValue e1 e2) True = Nothing



-- top level

typecheck :: CoreExpr -> Type
typecheck e = maybe (error "typecheck") fst (sequentcheck ([], []) ([], []) e)

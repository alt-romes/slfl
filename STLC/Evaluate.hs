module Evaluate where

import CoreSyntax
import LinearCheck hiding (BoundCtxt, FreeCtxt, Ctxt, equalCtxts)

type BoundCtxt = [CoreExpr]
type FreeCtxt = [(Name, CoreExpr)]
type Ctxt = (BoundCtxt, FreeCtxt)

-- evaluate --- Ctxt, CoreExpr -> CoreExpr 
-- typechecker should make sure the expression is valid
evaluate :: Ctxt -> CoreExpr -> CoreExpr

--- hyp --------------------

evaluate (bctxt, fctxt) (BLVar x) = bctxt !! x

evaluate (bctxt, fctxt) (FLVar x) = fromJust $ lookup x fctxt

evaluate (bctxt, fctxt) (BUVar x) = bctxt !! x

evaluate (bctxt, fctxt) (FUVar x) = fromJust $ lookup x fctxt

--- -o ---------------------

--  -oI
evaluate ctxt (Abs t e) = -- todo; rever gestão recursos
    return $ Abs t e

--  -oE
evaluate ctxt (App e1 e2) = do
    (Abs _ e1', del1) <- evaluate ctxt e1
    (v, del2) <- evaluate ctxt e2
    return (, del2)

--- * ----------------------

--  *I
evaluate depth gam del (TensorValue e1 e2) = do
    (t1, del2) <- evaluate depth gam del e1
    (t2, del3) <- evaluate depth gam del2 e2
    return (Tensor t1 t2, del3)

--  *E
evaluate depth gam del (LetTensor e1 e2) = do
    (Tensor t1 t2, (bdel', fdel')) <- evaluate depth gam del e1
    (t3, del3) <- evaluate (depth+2) gam ((depth, t1):((depth+1, t2):bdel'), fdel') e2
    return (t3, del3)

--- 1 ----------------------

--  1I
evaluate depth gam del UnitValue = return (Unit, del)

--  1E
evaluate depth gam del (LetUnit e1 e2) = do
    (Unit, del2) <- evaluate depth gam del e1
    (t2, del3) <- evaluate depth gam del2 e2
    return (t2, del3)

--- & ----------------------

--  &I
evaluate depth gam del (WithValue e1 e2) = do
    (t1, del2) <- evaluate depth gam del e1
    (t2, del3) <- evaluate depth gam del e2
    if del2 == del3 then return (With t1 t2, del2)
    else Nothing

--  &E
evaluate depth gam del (Fst e) = do
    (With t1 t2, del2) <- evaluate depth gam del e
    return (t1, del2)

--  &E
evaluate depth gam del (Snd e) = do
    (With t1 t2, del2) <- evaluate depth gam del e
    return (t2, del2)

--- + ----------------------

--  +I
evaluate depth gam del (InjL t1 e) = do
    (t2, del2) <- evaluate depth gam del e
    return (Plus t2 t1, del2)

--  +I
evaluate depth gam del (InjR t1 e) = do
    (t2, del2) <- evaluate depth gam del e
    return (Plus t1 t2, del2)

--  +E
evaluate depth gam del (CaseOfPlus e1 e2 e3) = do
    (Plus t1 t2, (bdel', fdel')) <- evaluate depth gam del e1
    (t3, del3) <- evaluate (depth+1) gam ((depth, t1):bdel', fdel') e2
    (t4, del4) <- evaluate (depth+1) gam ((depth, t2):bdel', fdel') e3
    if t3 == t4 && equalCtxts del3 del4
       then return (t4, del4)
       else Nothing

--- ! ----------------------

--  !I
evaluate depth gam del (BangValue e) = do
    (t2, del2) <- evaluate depth gam del e
    if del2 /= del then Nothing
    else return (Bang t2, del)

--  !E
evaluate depth (bgam, fgam) del (LetBang e1 e2) = do
    (Bang t1, del2) <- evaluate depth (bgam, fgam) del e1
    evaluate (depth+1) ((depth, t1):bgam, fgam) del2 e2


--- ? ----------------------

-- Onde é que estas regras se enquadram? Como é que lhes chamamos?
evaluate depth gam del Tru = return (Bool, del)
evaluate depth gam del Fls = return (Bool, del)

evaluate depth gam del (IfThenElse e1 e2 e3) = do
    (Bool, del1) <- evaluate depth gam del e1
    (t2, del2) <- evaluate depth gam del1 e2
    (t3, del3) <- evaluate depth gam del1 e3
    if t2 == t3 && equalCtxts del2 del3 -- TODO: está correto?
       then return (t3, del3)
       else Nothing

-- end evaluate ------------



-- util --------------------

-- todo: como organizar os ficheiros? neste momento estou a usar
-- o findDelete do typechecker

equalCtxts :: Ctxt -> Ctxt -> Bool
equalCtxts (a, a') (b, b') = a == b && a' == b'

-- top level ---------------


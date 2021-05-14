module LinearCheck where

import Data.Maybe
import Data.Bifunctor
import Debug.Trace

import CoreSyntax

type TypeBinding = (String, Type)


type Index = Int
type Name = String

type BoundCtxt = [Maybe Type]
type FreeCtxt = [(Name, Type)]
type Ctxt = (BoundCtxt, FreeCtxt)


lincheck :: Ctxt -> CoreExpr -> Maybe (Type, Ctxt)

--- hyp --------------------

lincheck ctxt (BLVar x) = do
    let (pre, maybet:end) = splitAt x $ fst ctxt
    t <- maybet
    return (t, (pre ++ Nothing:end, snd ctxt))

lincheck (bctxt, fctxt) (FLVar x) = do
    let (maybet, fctxt') = findDelete x fctxt []
    t <- maybet
    return (t, (bctxt, fctxt'))

lincheck ctxt (BUVar x) = do
    t <- fst ctxt !! x
    return (t, ctxt)

lincheck ctxt (FUVar x) = do
    t <- lookup x $ snd ctxt
    return (t, ctxt)

--- -o ---------------------

--  -oI
lincheck (bdel, fdel) (Abs t1 e) = do
    (t2, del2) <- lincheck (Just t1:bdel, fdel) e
    return (Fun t1 t2, del2)

--  -oE
lincheck del (App e1 e2) = do
    (Fun t1 t2, del1) <- lincheck del e1
    (t, del2) <- lincheck del1 e2
    if t == t1
        then return (t2, del2)
        else Nothing

--- * ----------------------

--  *I
lincheck del (TensorValue e1 e2) = do
    (t1, del2) <- lincheck del e1
    (t2, del3) <- lincheck del2 e2
    return (Tensor t1 t2, del3)

--  *E
lincheck del (LetTensor e1 e2) = do
    (Tensor t1 t2, (bdel', fdel')) <- lincheck del e1
    (t3, del3) <- lincheck (Just t2:Just t1:bdel', fdel') e2
    return (t3, del3)

--- 1 ----------------------

--  1I
lincheck del UnitValue = return (Unit, del)

--  1E
lincheck del (LetUnit e1 e2) = do
    (Unit, del2) <- lincheck del e1
    (t2, del3) <- lincheck del2 e2
    return (t2, del3)

--- & ----------------------

--  &I
lincheck del (WithValue e1 e2) = do
    (t1, del2) <- lincheck del e1
    (t2, del3) <- lincheck del e2
    if equalCtxts del2 del3
        then return (With t1 t2, del2)
        else Nothing

--  &E
lincheck del (Fst e) = do
    (With t1 t2, del2) <- lincheck del e
    return (t1, del2)

--  &E
lincheck del (Snd e) = do
    (With t1 t2, del2) <- lincheck del e
    return (t2, del2)

--- + ----------------------

--  +I
lincheck del (InjL t1 e) = do
    (t2, del2) <- lincheck del e
    return (Plus t2 t1, del2)

--  +I
lincheck del (InjR t1 e) = do
    (t2, del2) <- lincheck del e
    return (Plus t1 t2, del2)

--  +E
lincheck del (CaseOfPlus e1 e2 e3) = do
    (Plus t1 t2, (bdel', fdel')) <- lincheck del e1
    (t3, del3) <- lincheck (Just t1:bdel', fdel') e2
    (t4, del4) <- lincheck (Just t2:bdel', fdel') e3
    if t3 == t4 && equalCtxts del3 del4
       then return (t4, del4)
       else Nothing

--- ! ----------------------

--  !I
lincheck del (BangValue e) = do
    (t2, del2) <- lincheck del e
    if equalCtxts del2 del
        then return (Bang t2, del)
        else Nothing

--  !E
lincheck ctxt (LetBang e1 e2) = do
    (Bang t1, (bctxt', fctxt')) <- lincheck ctxt e1
    lincheck (Just t1:bctxt', fctxt') e2


--- Bool -------------------

lincheck del Tru = return (Bool, del)
lincheck del Fls = return (Bool, del)

lincheck del (IfThenElse e1 e2 e3) = do
    (Bool, del1) <- lincheck del e1
    (t2, del2) <- lincheck del1 e2
    (t3, del3) <- lincheck del1 e3
    if t2 == t3 && equalCtxts del2 del3
       then return (t3, del3)
       else Nothing

-- end lincheck ------------



-- util --------------------

findDelete :: (Eq a) => a -> [(a, b)] -> [(a, b)] -> (Maybe b, [(a, b)])
findDelete _ [] _ = (Nothing, [])
findDelete x ((y,t):xs) acc =
    if x==y then (Just t, reverse acc ++ xs)
    else findDelete x xs ((y,t):acc)

equalCtxts :: Ctxt -> Ctxt -> Bool
equalCtxts (ba, fa) (bb, fb) = (catMaybes ba, fa) == (catMaybes bb, fb)

-- top level ---------------

typecheck :: CoreExpr -> Type
typecheck e = maybe (error "[Typecheck] Failed") fst (lincheck ([], []) e)


typecheckModule :: [CoreBinding] -> [TypeBinding]
typecheckModule cbs = typecheckModule' cbs []
    where typecheckModule' cbs acc = 
            if null cbs then []
            else let (n, ce):xs = cbs in
                 let tb = (n, maybe (error ("[Typecheck Module] Failed when parsing " ++ show (n, ce) ++ " with accumulator " ++ show acc)) fst $ lincheck ([], acc) ce) in
                     tb:typecheckModule' xs (tb:acc)


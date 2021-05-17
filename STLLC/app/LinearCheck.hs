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
lincheck (bctx, fctx) (Abs t1 e) = do
    (t2, ctx2) <- lincheck (Just t1:bctx, fctx) e
    return (Fun t1 t2, ctx2)

--  -oE
lincheck ctx (App e1 e2) = do
    (Fun t1 t2, ctx1) <- lincheck ctx e1
    (t, ctx2) <- lincheck ctx1 e2
    if t == t1
        then return (t2, ctx2)
        else Nothing

--- * ----------------------

--  *I
lincheck ctx (TensorValue e1 e2) = do
    (t1, ctx2) <- lincheck ctx e1
    (t2, ctx3) <- lincheck ctx2 e2
    return (Tensor t1 t2, ctx3)

--  *E
lincheck ctx (LetTensor e1 e2) = do
    (Tensor t1 t2, (bctx', fctx')) <- lincheck ctx e1
    (t3, ctx3) <- lincheck (Just t2:Just t1:bctx', fctx') e2
    return (t3, ctx3)

--- 1 ----------------------

--  1I
lincheck ctx UnitValue = return (Unit, ctx)

--  1E
lincheck ctx (LetUnit e1 e2) = do
    (Unit, ctx2) <- lincheck ctx e1
    (t2, ctx3) <- lincheck ctx2 e2
    return (t2, ctx3)

--- & ----------------------

--  &I
lincheck ctx (WithValue e1 e2) = do
    (t1, ctx2) <- lincheck ctx e1
    (t2, ctx3) <- lincheck ctx e2
    if equalCtxts ctx2 ctx3
        then return (With t1 t2, ctx2)
        else Nothing

--  &E
lincheck ctx (Fst e) = do
    (With t1 t2, ctx2) <- lincheck ctx e
    return (t1, ctx2)

--  &E
lincheck ctx (Snd e) = do
    (With t1 t2, ctx2) <- lincheck ctx e
    return (t2, ctx2)

--- + ----------------------

--  +I
lincheck ctx (InjL t1 e) = do
    (t2, ctx2) <- lincheck ctx e
    return (Plus t2 t1, ctx2)

--  +I
lincheck ctx (InjR t1 e) = do
    (t2, ctx2) <- lincheck ctx e
    return (Plus t1 t2, ctx2)

--  +E
lincheck ctx (CaseOfPlus e1 e2 e3) = do
    (Plus t1 t2, (bctx', fctx')) <- lincheck ctx e1
    (t3, ctx3) <- lincheck (Just t1:bctx', fctx') e2
    (t4, ctx4) <- lincheck (Just t2:bctx', fctx') e3
    if t3 == t4 && equalCtxts ctx3 ctx4
       then return (t4, ctx4)
       else Nothing

--- ! ----------------------

--  !I
lincheck ctx (BangValue e) = do
    (t2, ctx2) <- lincheck ctx e
    if equalCtxts ctx2 ctx
        then return (Bang t2, ctx)
        else Nothing

--  !E
lincheck ctxt (LetBang e1 e2) = do
    (Bang t1, (bctxt', fctxt')) <- lincheck ctxt e1
    lincheck (Just t1:bctxt', fctxt') e2

--- LetIn ------------------

lincheck c (LetIn e1 e2) = do
    (t1, c'@(bc, fc)) <- lincheck c e1
    (t2, c'') <- lincheck (Just t1:bc, fc) e2
    return (t2, c'')

--- Bool -------------------

lincheck ctx Tru = return (Bool, ctx)
lincheck ctx Fls = return (Bool, ctx)

lincheck ctx (IfThenElse e1 e2 e3) = do
    (Bool, ctx1) <- lincheck ctx e1
    (t2, ctx2) <- lincheck ctx1 e2
    (t3, ctx3) <- lincheck ctx1 e3
    if t2 == t3 && equalCtxts ctx2 ctx3
       then return (t3, ctx3)
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
                 let tb = (n, maybe (error ("[Typecheck Module] Failed when checking " ++ show (n, ce) ++ " with accumulator " ++ show acc)) fst $ lincheck ([], acc) ce) in
                     tb:typecheckModule' xs (tb:acc)


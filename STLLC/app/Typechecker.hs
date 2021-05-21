module Typechecker where

import Control.Applicative
import Data.Maybe
import Control.Monad.State
import Data.Bifunctor

import CoreSyntax

data TypeBinding = TypeBinding String Type
instance (Show TypeBinding) where
    show (TypeBinding s e) = s ++ ":\n    " ++ show e ++ "\n"

type BoundCtxt = [Maybe Type]
type FreeCtxt = [(String, Type)]
type Ctxt = (BoundCtxt, FreeCtxt)

data Constraint = Constraint Type Type -- e.g. [X -> Y] [X -> Y -> X]


-- Generate a list of constraints, a type that may have type varibales, and a modified expression with type variables instead of nothing for untyped types
typeconstraint :: [Constraint] -> Ctxt -> CoreExpr -> StateT Int Maybe (Type, CoreExpr, Ctxt, [Constraint])

--- hyp --------------------

typeconstraint constraints ctxt ce@(BLVar x) = do
    let (pre, maybet:end) = splitAt x $ fst ctxt
    t <- lift maybet
    return (t, ce, (pre ++ Nothing:end, snd ctxt), constraints)

typeconstraint constraints (bctxt, fctxt) ce@(FLVar x) = do
    let (maybet, fctxt') = findDelete x fctxt []
    t <- lift maybet
    return (t, ce, (bctxt, fctxt'), constraints)

typeconstraint constraints ctxt ce@(BUVar x) = do
    t <- lift $ fst ctxt !! x
    return (t, ce, ctxt, constraints)

typeconstraint constraints ctxt ce@(FUVar x) = do
    t <- lift $ lookup x $ snd ctxt
    return (t, ce, ctxt, constraints)

--- -o ---------------------

--  -oI
typeconstraint constraints (bctx, fctx) (Abs t1 e) = do
    vari <- get
    put $ vari + 1
    let t1' = fromMaybe (TypeVar vari) t1
    (t2, ce, ctx2, constraints') <- typeconstraint constraints (Just t1':bctx, fctx) e
    return (Fun t1' t2, Abs (Just t1') ce, ctx2, constraints')

--  -oE
typeconstraint constraints ctx (App e1 e2) = do
    vari <- get
    put (vari+1)
    (t1, ce1, ctx1, constraints') <- typeconstraint constraints ctx e1
    (t2, ce2, ctx2, constraints'') <- typeconstraint constraints' ctx1 e2
    return (t2, App ce1 ce2, ctx2, Constraint t1 (Fun t2 (TypeVar vari)):constraints'')

--- * ----------------------

--  *I
typeconstraint constraints ctx (TensorValue e1 e2) = do
    (t1, ce1, ctx2, constraints') <- typeconstraint constraints ctx e1
    (t2, ce2, ctx3, constraints'') <- typeconstraint constraints' ctx2 e2
    return (Tensor t1 t2, TensorValue ce1 ce2, ctx3, constraints'')

--  *E
typeconstraint constraints ctx (LetTensor e1 e2) = do
    vari <- get
    let tv1 = TypeVar vari
    let tv2 = TypeVar $ vari+1
    put $ vari+2
    (t, ce1, (bctx', fctx'), constraints') <- typeconstraint constraints ctx e1
    (t3, ce2, ctx3, constraints'') <- typeconstraint constraints' (Just tv2:Just tv1:bctx', fctx') e2
    return (t3, LetTensor ce1 ce2, ctx3, Constraint t (Tensor tv1 tv2):constraints'')

--- 1 ----------------------

--  1I
typeconstraint constraints ctx UnitValue = return (Unit, UnitValue, ctx, constraints)

--  1E
typeconstraint constraints ctx (LetUnit e1 e2) = do
    (t1, ce1, ctx2, constraints') <- typeconstraint constraints ctx e1
    (t2, ce2, ctx3, constraints'') <- typeconstraint constraints' ctx2 e2
    return (t2, LetUnit ce1 ce2, ctx3, Constraint t1 Unit:constraints'')

--- & ----------------------

--  &I
typeconstraint constraints ctx (WithValue e1 e2) = do
    (t1, ce1, ctx2, constraints') <- typeconstraint constraints ctx e1
    (t2, ce2, ctx3, constraints'') <- typeconstraint constraints' ctx e2
    if equalCtxts ctx2 ctx3
        then return (With t1 t2, WithValue ce1 ce2, ctx2, constraints'')
        else empty

--  &E
typeconstraint constraints ctx (Fst e) = do
    vari <- get
    let tv1 = TypeVar vari
    let tv2 = TypeVar $ vari+1
    put $ vari+2
    (t, ce, ctx2, constraints') <- typeconstraint constraints ctx e
    return (tv1, Fst ce, ctx2, Constraint t (With tv1 tv2):constraints')

--  &E
typeconstraint constraints ctx (Snd e) = do
    vari <- get
    let tv1 = TypeVar vari
    let tv2 = TypeVar $ vari+1
    put $ vari+2
    (t, ce, ctx2, constraints') <- typeconstraint constraints ctx e
    return (tv2, Snd ce, ctx2, Constraint t (With tv1 tv2):constraints')

--- + ----------------------

--  +I
typeconstraint constraints ctx (InjL t1 e) = do 
    vari <- get
    put $ vari+1 -- TODO: Assim as variáveis de tipo vão avançar mesmo que não sejam usadas, é OK não é? para não repetir código e fazer patternmatch do nothing e just t separado
    let t1' = fromMaybe (TypeVar vari) t1
    (t2, ce, ctx2, constraints') <- typeconstraint constraints ctx e
    return (Plus t2 t1', InjL (Just t1') ce, ctx2, constraints')

--  +I
typeconstraint constraints ctx (InjR t1 e) = do
    vari <- get
    put $ vari+1 -- TODO: Assim as variáveis de tipo vão avançar mesmo que não sejam usadas, é OK não é? para não repetir código e fazer patternmatch do nothing e just t separado
    let t1' = fromMaybe (TypeVar vari) t1
    (t2, ce, ctx2, constraints') <- typeconstraint constraints ctx e
    return (Plus t1' t2, InjR (Just t1') ce, ctx2, constraints')

--  +E
typeconstraint constraints ctx (CaseOfPlus e1 e2 e3) = do
    (pt, ce1, (bctx', fctx'), constraints') <- typeconstraint constraints ctx e1
    vari <- get
    let tv1 = TypeVar vari
    let tv2 = TypeVar $ vari+1
    put $ vari+2
    (t3, ce2, ctx3, constraints') <- typeconstraint constraints' (Just tv1:bctx', fctx') e2
    (t4, ce3, ctx4, constraints'') <- typeconstraint constraints' (Just tv2:bctx', fctx') e3
    if equalCtxts ctx3 ctx4
       then return (t4, CaseOfPlus ce1 ce2 ce3, ctx4, Constraint t3 t4:Constraint pt (Plus tv1 tv2):constraints'')
       else empty

--- ! ----------------------

--  !I
typeconstraint constraints ctx (BangValue e) = do
    (t2, ce, ctx2, constraints') <- typeconstraint constraints ctx e
    if equalCtxts ctx2 ctx
        then return (Bang t2, BangValue ce, ctx, constraints')
        else empty

--  !E
typeconstraint constraints ctxt (LetBang e1 e2) = do
    (t1, ce1, (bctxt', fctxt'), constraints') <- typeconstraint constraints ctxt e1
    vari <- get
    put $ vari + 1
    let tv1 = TypeVar vari
    (t2, ce2, ctxt'', constraints'') <- typeconstraint constraints' (Just tv1:bctxt', fctxt') e2
    return (t2, LetBang ce1 ce2, ctxt'', Constraint t1 (Bang tv1):constraints'')

--- LetIn ------------------

typeconstraint constraints c (LetIn e1 e2) = do
    (t1, ce1, c'@(bc, fc), constraints') <- typeconstraint constraints c e1
    (t2, ce2, c'', constraints'') <- typeconstraint constraints' (Just t1:bc, fc) e2
    return (t2, LetIn ce1 ce2, c'', constraints'')

--- Bool -------------------

typeconstraint constraints ctx Tru = return (Bool, Tru, ctx, constraints)
typeconstraint constraints ctx Fls = return (Bool, Fls, ctx, constraints)

typeconstraint constraints ctx (IfThenElse e1 e2 e3) = do
    (t1, ce1, ctx1, constraints') <- typeconstraint constraints ctx e1
    (t2, ce2, ctx2, constraints'') <- typeconstraint constraints' ctx1 e2
    (t3, ce3, ctx3, constraints'') <- typeconstraint constraints'' ctx1 e3
    if equalCtxts ctx2 ctx3
       then return (t3, IfThenElse ce1 ce2 ce3, ctx3, Constraint t2 t3:Constraint t1 Bool:constraints'')
       else empty

--- Synth marker ---

typeconstraint constraints ctx (Mark t) = do
    vari <- get
    put $ vari + 1
    let t' = fromMaybe (TypeVar vari) t
    return (t', Mark (Just t'), ctx, constraints)

-- end typeconstrain ------------

-- solveconstraints :: [Constraint] -> 


-- util --------------------

findDelete :: (Eq a) => a -> [(a, b)] -> [(a, b)] -> (Maybe b, [(a, b)])
findDelete _ [] _ = (Nothing, [])
findDelete x ((y,t):xs) acc =
    if x==y then (Just t, reverse acc ++ xs)
    else findDelete x xs ((y,t):acc)

equalCtxts :: Ctxt -> Ctxt -> Bool
equalCtxts (ba, fa) (bb, fb) = (catMaybes ba, fa) == (catMaybes bb, fb)



---- TOP LEVEL ------------

typecheckExpr :: CoreExpr -> Type
typecheckExpr e = maybe (errorWithoutStackTrace "[Typecheck] Failed") fst (typecheck ([], []) e)

typecheckModule :: [CoreBinding] -> [TypeBinding]
typecheckModule cbs = typecheckModule' cbs []
    where typecheckModule' cbs acc = 
            if null cbs then []
            else let b@(CoreBinding n ce):xs = cbs in
                 let tb = TypeBinding n $ maybe (errorWithoutStackTrace ("[Typecheck Module] Failed checking: " ++ show b)) fst $ typecheck ([], map (\(TypeBinding n t) -> (n, t)) acc) ce in
                     tb:typecheckModule' xs (tb:acc)


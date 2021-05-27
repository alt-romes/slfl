module Typechecker where

import Control.Applicative
import Data.Maybe
import Data.List (sortBy)
import Control.Monad.State
import Control.Monad.Writer (WriterT, writer, runWriterT) 
import Data.Bifunctor
import qualified Data.Map as Map
import Debug.Trace

import CoreSyntax

data TypeBinding = TypeBinding String Type
instance (Show TypeBinding) where
    show (TypeBinding s e) = s ++ ":\n    " ++ show e ++ "\n"

type BoundCtxt = [Maybe Type]
type FreeCtxt = [(String, Type)]
type Ctxt = (BoundCtxt, FreeCtxt)

data Constraint = Constraint Type Type -- e.g. [X => Y]
instance Show Constraint where
    show (Constraint t t') = "[" ++ show t ++ " => " ++ show t' ++ "]"

type Substitution = (Type, CoreExpr) -> (Type, CoreExpr) -- F to replace all type variables with interpreted types

type Infer = WriterT [Constraint] (StateT Int Maybe)

-- Generate a list of constraints, a type that may have type varibales, and a modified expression with type variables instead of nothing for untyped types
typeconstraint :: Ctxt -> CoreExpr -> Infer (Type, CoreExpr, Ctxt)

--- hyp --------------------

typeconstraint ctxt ce@(BLVar x) = do
    let (pre, maybet:end) = splitAt x $ fst ctxt
    t <- lift $ lift maybet
    return (t, ce, (pre ++ Nothing:end, snd ctxt))

typeconstraint (bctxt, fctxt) ce@(FLVar x) = do
    let (maybet, fctxt') = findDelete x fctxt []
    t <- lift $ lift maybet
    return (t, ce, (bctxt, fctxt'))

typeconstraint ctxt ce@(BUVar x) = do
    t <- lift $ lift $ fst ctxt !! x
    return (t, ce, ctxt)

typeconstraint ctxt ce@(FUVar x) = do
    t <- lift $ lift $ lookup x $ snd ctxt
    return (t, ce, ctxt)

--- -o ---------------------

--  -oI
typeconstraint (bctx, fctx) (Abs t1 e) = do
    vari <- get
    put $ vari + 1
    let t1' = fromMaybe (TypeVar vari) t1
    (t2, ce, ctx2) <- typeconstraint (Just t1':bctx, fctx) e
    return (Fun t1' t2, Abs (Just t1') ce, ctx2)

--  -oE
typeconstraint ctx (App e1 e2) = do
    vari <- get
    put (vari+1)
    let tv = TypeVar vari
    (t1, ce1, ctx1) <- typeconstraint ctx e1
    (t2, ce2, ctx2) <- typeconstraint ctx1 e2
    writer ((tv, App ce1 ce2, ctx2), [Constraint t1 (Fun t2 tv)])

--- * ----------------------

--  *I
typeconstraint ctx (TensorValue e1 e2) = do
    (t1, ce1, ctx2) <- typeconstraint ctx e1
    (t2, ce2, ctx3) <- typeconstraint ctx2 e2
    return (Tensor t1 t2, TensorValue ce1 ce2, ctx3)

--  *E
typeconstraint ctx (LetTensor e1 e2) = do
    vari <- get
    let tv1 = TypeVar vari
    let tv2 = TypeVar $ vari+1
    put $ vari+2
    (t, ce1, (bctx', fctx')) <- typeconstraint ctx e1
    (t3, ce2, ctx3) <- typeconstraint (Just tv2:Just tv1:bctx', fctx') e2
    writer ((t3, LetTensor ce1 ce2, ctx3), [Constraint t (Tensor tv1 tv2)])

--- 1 ----------------------

--  1I
typeconstraint ctx UnitValue = return (Unit, UnitValue, ctx)

--  1E
typeconstraint ctx (LetUnit e1 e2) = do
    (t1, ce1, ctx2) <- typeconstraint ctx e1
    (t2, ce2, ctx3) <- typeconstraint ctx2 e2
    writer ((t2, LetUnit ce1 ce2, ctx3), [Constraint t1 Unit])

--- & ----------------------

--  &I
typeconstraint ctx (WithValue e1 e2) = do
    (t1, ce1, ctx2) <- typeconstraint ctx e1
    (t2, ce2, ctx3) <- typeconstraint ctx e2
    if equalCtxts ctx2 ctx3
        then return (With t1 t2, WithValue ce1 ce2, ctx2)
        else empty

--  &E
typeconstraint ctx (Fst e) = do
    vari <- get
    let tv1 = TypeVar vari
    let tv2 = TypeVar $ vari+1
    put $ vari+2
    (t, ce, ctx2) <- typeconstraint ctx e
    writer ((tv1, Fst ce, ctx2), [Constraint t (With tv1 tv2)])

--  &E
typeconstraint ctx (Snd e) = do
    vari <- get
    let tv1 = TypeVar vari
    let tv2 = TypeVar $ vari+1
    put $ vari+2
    (t, ce, ctx2) <- typeconstraint ctx e
    writer ((tv2, Snd ce, ctx2), [Constraint t (With tv1 tv2)])

--- + ----------------------

--  +I
typeconstraint ctx (InjL t1 e) = do 
    vari <- get
    put $ vari+1 -- TODO: Assim as variáveis de tipo vão avançar mesmo que não sejam usadas, é OK não é? para não repetir código e fazer patternmatch do nothing e just t separado
    let t1' = fromMaybe (TypeVar vari) t1
    (t2, ce, ctx2) <- typeconstraint ctx e
    return (Plus t2 t1', InjL (Just t1') ce, ctx2)

--  +I
typeconstraint ctx (InjR t1 e) = do
    vari <- get
    put $ vari+1 -- TODO: Assim as variáveis de tipo vão avançar mesmo que não sejam usadas, é OK não é? para não repetir código e fazer patternmatch do nothing e just t separado
    let t1' = fromMaybe (TypeVar vari) t1
    (t2, ce, ctx2) <- typeconstraint ctx e
    return (Plus t1' t2, InjR (Just t1') ce, ctx2)

--  +E
typeconstraint ctx (CaseOfPlus e1 e2 e3) = do
    (pt, ce1, (bctx', fctx')) <- typeconstraint ctx e1
    vari <- get
    let tv1 = TypeVar vari
    let tv2 = TypeVar $ vari+1
    put $ vari+2
    (t3, ce2, ctx3) <- typeconstraint (Just tv1:bctx', fctx') e2
    (t4, ce3, ctx4) <- typeconstraint (Just tv2:bctx', fctx') e3
    if equalCtxts ctx3 ctx4
       then writer ((t4, CaseOfPlus ce1 ce2 ce3, ctx4), [Constraint t3 t4, Constraint pt (Plus tv1 tv2)])
       else empty

--- ! ----------------------

--  !I
typeconstraint ctx (BangValue e) = do
    (t2, ce, ctx2) <- typeconstraint ctx e
    if equalCtxts ctx2 ctx
        then return (Bang t2, BangValue ce, ctx)
        else empty -- TODO: Assim (\x -o !x) não é sintetisado, mas se calhar o tipo inferido de x devia ser !a

--  !E
typeconstraint ctxt (LetBang e1 e2) = do
    (t1, ce1, (bctxt', fctxt')) <- typeconstraint ctxt e1
    vari <- get
    put $ vari + 1
    let tv1 = TypeVar vari
    (t2, ce2, ctxt'') <- typeconstraint (Just tv1:bctxt', fctxt') e2
    writer ((t2, LetBang ce1 ce2, ctxt''), [Constraint t1 (Bang tv1)])

--- LetIn ------------------

typeconstraint c (LetIn e1 e2) = do
    (t1, ce1, c'@(bc, fc)) <- typeconstraint c e1
    (t2, ce2, c'') <- typeconstraint (Just t1:bc, fc) e2
    return (t2, LetIn ce1 ce2, c'')

--- Synth marker ---

typeconstraint ctx (Mark i t) = do
    vari <- get
    put $ vari + 1
    let t' = fromMaybe (TypeVar vari) t
    return (t', Mark i (Just t'), ctx)

--- Bool -------------------

typeconstraint ctx Tru = return (Bool, Tru, ctx)
typeconstraint ctx Fls = return (Bool, Fls, ctx)

-- TODO: if true then { ... } else false should synthetize a bool, but doesn't...
typeconstraint ctx (IfThenElse e1 e2 e3) = do
    (t1, ce1, ctx1) <- typeconstraint ctx e1
    (t2, ce2, ctx2) <- typeconstraint ctx1 e2
    (t3, ce3, ctx3) <- typeconstraint ctx1 e3
    if equalCtxts ctx2 ctx3
       then writer ((t3, IfThenElse ce1 ce2 ce3, ctx3), [Constraint t2 t3, Constraint t1 Bool])
       else empty

typeconstraint ctx (SumValue mts (t, e)) = do
    types <- mapM (\(s, mt) -> do
        vari <- get
        put $ vari + 1
        let t' = fromMaybe (TypeVar vari) mt
        return (s, t')) mts
    (t2, ce, ctx2) <- typeconstraint ctx e
    return (Sum ((t, t2):types), SumValue (map (second Just) types) (t, ce), ctx2)

typeconstraint ctx (CaseOfSum e exps) = do
    (st, ce, (bctx', fctx')) <- typeconstraint ctx e
    inferredexps <- mapM (\(s, ex) -> do
        vari <- get
        let tv = TypeVar vari
        put $ vari + 1
        (t', ce, ctx') <- typeconstraint (Just tv:bctx', fctx') ex
        return (t', s, ce, ctx')
        ) exps
    -- TODO: Probably doable in a more idiomatic way, like making an inference monad instead of all these function parameters
    let (t1', s1, ce1, ctx1') = head inferredexps
    if all ((== ctx1') . (\(_,_,_,c) -> c)) (tail inferredexps)
       then writer ((t1', CaseOfSum ce (map (\(_,s,c,_) -> (s,c)) inferredexps), ctx1'), Constraint st (Sum (map (\(t,s,_,_) -> (s, t)) inferredexps)):map (\(t'',_,_,_) -> Constraint t1' t'') (tail inferredexps))
       else empty

--- end typeconstraint ----------

type Subst = Map.Map Int Type

class Substitutable a where
    apply :: Subst -> a -> a

instance Substitutable Type where
    apply s (Fun t1 t2) = Fun (apply s t1) (apply s t2)
    apply s (Tensor t1 t2) = Tensor (apply s t1) (apply s t2)
    apply s (With t1 t2) = With (apply s t1) (apply s t2)
    apply s (Plus t1 t2) = Plus (apply s t1) (apply s t2)
    apply s (Bang t) = Bang (apply s t)
    apply s t@(TypeVar i) = Map.findWithDefault t i s
    apply s (Sum tl) = Sum $ map (second $ apply s) tl
    apply s t = t

instance Substitutable CoreExpr where
    apply s (Abs (Just t) e) = Abs (return $ apply s t) (apply s e)
    apply s (App e1 e2) = App (apply s e1) (apply s e2)
    apply s (TensorValue e1 e2) = TensorValue (apply s e1) (apply s e2)
    apply s (LetTensor e1 e2) = LetTensor (apply s e1) (apply s e2)
    apply s (LetUnit e1 e2) = LetUnit (apply s e1) (apply s e2)
    apply s (WithValue e1 e2) = WithValue (apply s e1) (apply s e2)
    apply s (Fst e) = Fst (apply s e)
    apply s (Snd e) = Snd (apply s e)
    apply s (InjL (Just t) e) = InjL (return $ apply s t) (apply s e)
    apply s (InjR (Just t) e) = InjR (return $ apply s t) (apply s e)
    apply s (CaseOfPlus e1 e2 e3) = CaseOfPlus (apply s e1) (apply s e2) (apply s e3)
    apply s (Mark i (Just t)) = Mark i (return $ apply s t)
    apply s (SumValue tl (i, e)) = SumValue (map (second $ apply s) tl) (i, apply s e)
    apply s (CaseOfSum e el) = CaseOfSum (apply s e) (map (second $ apply s) el)
    apply s e = e

instance Substitutable CoreBinding where
    apply s (CoreBinding n e') = CoreBinding n (apply s e')

instance Substitutable a => Substitutable (Maybe a) where
    apply s Nothing = Nothing
    apply s (Just t) = Just (apply s t)

instance Substitutable a => Substitutable [a] where
    apply s l = map (apply s) l

instance (Substitutable a, Substitutable b) => Substitutable ((,) a b) where
    apply s (x, y) = (apply s x, apply s y)

ftv :: [Int] -> Type -> [Int]
ftv acc (Fun t t') = ftv acc t ++ ftv acc t'
ftv acc (Tensor t t') = ftv acc t ++ ftv acc t'
ftv acc (With t t') = ftv acc t ++ ftv acc t'
ftv acc (Plus t t') = ftv acc t ++ ftv acc t'
ftv acc (Bang t) = ftv acc t
ftv acc (TypeVar x) = x:acc
ftv acc (Sum []) = acc
ftv acc (Sum ((i, t):ts)) = ftv acc t ++ ftv acc (Sum ts)
ftv acc t = acc

unify :: Type -> Type -> Maybe Subst 
unify Bool Bool = Just Map.empty
unify (Atom x) (Atom y) = if x == y then Just Map.empty else Nothing
unify Unit Unit = Just Map.empty
unify (TypeVar x) (TypeVar y) = if x == y then Just Map.empty else Just $ Map.singleton x (TypeVar y)
unify (TypeVar x) y = if x `notElem` ftv [] y then Just $ Map.singleton x y else Nothing
unify x (TypeVar y) = if y `notElem` ftv [] x then Just $ Map.singleton y x else Nothing
unify (Fun t1 t2) (Fun t1' t2') = do
    s  <- unify t1 t1'
    s' <- unify (apply s t2) (apply s t2')
    return $ compose s' s
unify (Tensor t1 t2) (Tensor t1' t2') = do
    s  <- unify t1 t1'
    s' <- unify (apply s t2) (apply s t2')
    return $ compose s' s
unify (With t1 t2) (With t1' t2') = do
    s  <- unify t1 t1'
    s' <- unify (apply s t2) (apply s t2')
    return $ compose s' s
unify (Plus t1 t2) (Plus t1' t2') = do
    s  <- unify t1 t1'
    s' <- unify (apply s t2) (apply s t2')
    return $ compose s' s
unify (Bang x) (Bang y) = unify x y
unify (Sum xtl) (Sum ytl) = do
    let xtl' = sortBy (\(a,_) (b,_) -> compare a b) xtl
    let ytl' = sortBy (\(a,_) (b,_) -> compare a b) ytl
    let maybesubs = zipWith (\x y -> snd x `unify` snd y) xtl' ytl'
    foldM (\p n -> compose p <$> n) Map.empty maybesubs

nify _ _ = Nothing

compose :: Subst -> Subst -> Subst
s' `compose` s = Map.map (apply s') s `Map.union` s'

solveconstraints :: Subst -> [Constraint] -> Maybe Subst -- w/ substitution accumulator and list of constraints generate a substitution
solveconstraints subs constr =
    case constr of
      [] -> return subs
      Constraint t1 t2:cs -> do
          s <- unify t1 t2
          solveconstraints (compose s subs) $ map (\(Constraint t1 t2) -> Constraint (apply s t1) (apply s t2)) cs


typeinfer :: FreeCtxt -> CoreExpr -> Maybe (Type, CoreExpr, Subst)
typeinfer fc e = do
    ((ctype, cexp, _), constraints) <- evalStateT (runWriterT $ typeconstraint ([], fc) e) (length fc)
    s <- solveconstraints Map.empty constraints
    let (ctype', cexp') = apply s (ctype, cexp)
    return (ctype', cexp', s)
        

--- util -------------------

findDelete :: (Eq a) => a -> [(a, b)] -> [(a, b)] -> (Maybe b, [(a, b)])
findDelete _ [] _ = (Nothing, [])
findDelete x ((y,t):xs) acc =
    if x==y then (Just t, reverse acc ++ xs)
    else findDelete x xs ((y,t):acc)

equalCtxts :: Ctxt -> Ctxt -> Bool
equalCtxts (ba, fa) (bb, fb) = (catMaybes ba, fa) == (catMaybes bb, fb) || trace "[Typecheck] Failed resource management." False



---- TOP LEVEL ------------

typeinferExpr :: CoreExpr -> CoreExpr
typeinferExpr e = maybe (errorWithoutStackTrace "[Typecheck] Failed") (\(_, ce, _) -> ce) (typeinfer [] e)

typeinferModule :: [CoreBinding] -> [CoreBinding] -- typecheck and use inferred types
typeinferModule cbs = let (finalcbs, finalsubst) = typeinferModule' cbs [] Map.empty in -- Infer and typecheck iteratively every expression, and in the end apply the final substitution (unified constraints) to all expressions
                          apply finalsubst finalcbs
    where
        typeinferModule' :: [CoreBinding] -> [TypeBinding] -> Subst -> ([CoreBinding], Subst)
        typeinferModule' corebindings acc subst =
            case corebindings of
              [] -> ([], subst)
              b@(CoreBinding n ce):corebindings' -> do
                 let (btype, bexpr, subst') =
                         fromMaybe (errorWithoutStackTrace ("[Typecheck Module] Failed checking: " ++ show b)) $
                             typeinfer (map (\(TypeBinding n t) -> (n, t)) acc) ce
                 first (CoreBinding n bexpr :) $ typeinferModule' corebindings' (TypeBinding n btype:acc) subst'

typecheckExpr :: CoreExpr -> Type
typecheckExpr e = maybe (errorWithoutStackTrace "[Typecheck] Failed") (\(t, _, _) -> t) (typeinfer [] e)

typecheckModule :: [CoreBinding] -> [TypeBinding]
typecheckModule cbs = typecheckModule' cbs []
    where typecheckModule' cbs acc = 
            if null cbs then []
            else let b@(CoreBinding n ce):xs = cbs in
                 let tb = TypeBinding n $ maybe (errorWithoutStackTrace ("[Typecheck Module] Failed checking: " ++ show b)) (\(t, _, _) -> t) $ typeinfer (map (\(TypeBinding n t) -> (n, t)) acc) ce in
                     tb:typecheckModule' xs (tb:acc)


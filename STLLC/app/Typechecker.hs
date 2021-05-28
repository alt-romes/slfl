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

type Infer = WriterT [Constraint] (StateT Ctxt (StateT Int Maybe))

-- Generate a list of constraints, a type that may have type varibales, and a modified expression with type variables instead of nothing for untyped types
typeconstraint :: CoreExpr -> Infer (Type, CoreExpr)

--- hyp --------------------

typeconstraint ce@(BLVar x) = do
    ctx <- get
    let (pre, maybet:end) = splitAt x $ fst ctx
    t <- lift $ lift $ lift maybet
    put (pre ++ Nothing:end, snd ctx)
    return (t, ce)

typeconstraint ce@(FLVar x) = do
    (bctx, fctx) <- get
    let (maybet, fctx') = findDelete x fctx []
    t <- lift $ lift $ lift maybet
    put (bctx, fctx')
    return (t, ce)

typeconstraint ce@(BUVar x) = do
    ctx <- get
    t <- lift $ lift $ lift $ fst ctx !! x
    return (t, ce)

typeconstraint ce@(FUVar x) = do
    ctx <- get
    t <- lift $ lift $ lift $ lookup x $ snd ctx
    return (t, ce)

--- -o ---------------------

--  -oI
typeconstraint (Abs t1 e) = do
    vari <- lift $ lift get
    lift $ lift $ put $ vari + 1
    let t1' = fromMaybe (TypeVar vari) t1
    (bctx, fctx) <- get
    put (Just t1':bctx, fctx)
    (t2, ce) <- typeconstraint e
    return (Fun t1' t2, Abs (Just t1') ce)

--  -oE
typeconstraint (App e1 e2) = do
    vari <- lift $ lift get
    lift $ lift $ put (vari+1)
    let tv = TypeVar vari
    (t1, ce1) <- typeconstraint e1
    (t2, ce2) <- typeconstraint e2
    writer ((tv, App ce1 ce2), [Constraint t1 (Fun t2 tv)])

--- * ----------------------

--  *I
typeconstraint (TensorValue e1 e2) = do
    (t1, ce1) <- typeconstraint e1
    (t2, ce2) <- typeconstraint e2
    return (Tensor t1 t2, TensorValue ce1 ce2)

--  *E
typeconstraint (LetTensor e1 e2) = do
    vari <- lift $ lift get
    let tv1 = TypeVar vari
    let tv2 = TypeVar $ vari+1
    lift $ lift $ put $ vari+2
    (t, ce1) <- typeconstraint e1
    (bctx, fctx) <- get
    put (Just tv2:Just tv1:bctx, fctx)
    (t3, ce2) <- typeconstraint e2
    writer ((t3, LetTensor ce1 ce2), [Constraint t (Tensor tv1 tv2)])

--- 1 ----------------------

--  1I
typeconstraint UnitValue = return (Unit, UnitValue)

--  1E
typeconstraint (LetUnit e1 e2) = do
    (t1, ce1) <- typeconstraint e1
    (t2, ce2) <- typeconstraint e2
    writer ((t2, LetUnit ce1 ce2), [Constraint t1 Unit])

--- & ----------------------

--  &I
typeconstraint (WithValue e1 e2) = do
    (t1, ce1) <- typeconstraint e1
    ctx2 <- get
    (t2, ce2) <- typeconstraint e2
    ctx3 <- get
    if equalCtxts ctx2 ctx3
        then return (With t1 t2, WithValue ce1 ce2)
        else empty

--  &E
typeconstraint (Fst e) = do
    vari <- lift $ lift get
    let tv1 = TypeVar vari
    let tv2 = TypeVar $ vari+1
    lift $ lift $ put $ vari+2
    (t, ce) <- typeconstraint e
    writer ((tv1, Fst ce), [Constraint t (With tv1 tv2)])

--  &E
typeconstraint (Snd e) = do
    vari <- lift $ lift get
    let tv1 = TypeVar vari
    let tv2 = TypeVar $ vari+1
    lift $ lift $ put $ vari+2
    (t, ce) <- typeconstraint e
    writer ((tv2, Snd ce), [Constraint t (With tv1 tv2)])

--- + ----------------------

--  +I
typeconstraint (InjL t1 e) = do 
    vari <- lift $ lift get
    lift $ lift $ put $ vari+1 -- TODO: Assim as variáveis de tipo vão avançar mesmo que não sejam usadas, é OK não é? para não repetir código e fazer patternmatch do nothing e just t separado
    let t1' = fromMaybe (TypeVar vari) t1
    (t2, ce) <- typeconstraint e
    return (Plus t2 t1', InjL (Just t1') ce)

--  +I
typeconstraint (InjR t1 e) = do
    vari <- lift $ lift get
    lift $ lift $ put $ vari+1 -- TODO: Assim as variáveis de tipo vão avançar mesmo que não sejam usadas, é OK não é? para não repetir código e fazer patternmatch do nothing e just t separado
    let t1' = fromMaybe (TypeVar vari) t1
    (t2, ce) <- typeconstraint e
    return (Plus t1' t2, InjR (Just t1') ce)

--  +E
typeconstraint (CaseOfPlus e1 e2 e3) = do
    (pt, ce1) <- typeconstraint e1
    vari <- lift $ lift get
    let tv1 = TypeVar vari
    let tv2 = TypeVar $ vari+1
    lift $ lift $ put $ vari+2
    (bctx, fctx) <- get
    put (Just tv1:bctx, fctx)
    (t3, ce2) <- typeconstraint  e2
    ctx3 <- get
    put (Just tv2:bctx, fctx)
    (t4, ce3) <- typeconstraint  e3
    ctx4 <- get
    if equalCtxts ctx3 ctx4
       then writer ((t4, CaseOfPlus ce1 ce2 ce3), [Constraint t3 t4, Constraint pt (Plus tv1 tv2)])
       else empty

--- ! ----------------------

--  !I
typeconstraint (BangValue e) = do
    ctx <- get
    (t2, ce) <- typeconstraint e
    ctx2 <- get
    if equalCtxts ctx2 ctx
        then return (Bang t2, BangValue ce)
        else empty -- TODO: Assim (\x -o !x) não é sintetisado, mas se calhar o tipo inferido de x devia ser !a

--  !E
typeconstraint (LetBang e1 e2) = do
    (t1, ce1) <- typeconstraint e1
    vari <- lift $ lift get
    lift $ lift $ put $ vari + 1
    let tv1 = TypeVar vari
    (bctx, fctx) <- get
    put (Just tv1:bctx, fctx)
    (t2, ce2) <- typeconstraint e2
    writer ((t2, LetBang ce1 ce2), [Constraint t1 (Bang tv1)])

--- LetIn ------------------

typeconstraint (LetIn e1 e2) = do
    (t1, ce1) <- typeconstraint e1
    (bctx, fctx) <- get
    put (Just t1:bctx, fctx)
    (t2, ce2) <- typeconstraint e2
    return (t2, LetIn ce1 ce2)

--- Synth marker ---

typeconstraint (Mark i t) = do
    vari <- lift $ lift get
    lift $ lift $ put $ vari + 1
    let t' = fromMaybe (TypeVar vari) t
    return (t', Mark i (Just t'))

--- Bool -------------------

typeconstraint Tru = return (Bool, Tru)
typeconstraint Fls = return (Bool, Fls)

-- TODO: if true then { ... } else false should synthetize a bool, but doesn't...
typeconstraint (IfThenElse e1 e2 e3) = do
    (t1, ce1) <- typeconstraint e1
    ctx1 <- get
    (t2, ce2) <- typeconstraint e2
    ctx2 <- get
    put ctx1
    (t3, ce3) <- typeconstraint e3
    ctx3 <- get
    if equalCtxts ctx2 ctx3
       then writer ((t3, IfThenElse ce1 ce2 ce3), [Constraint t2 t3, Constraint t1 Bool])
       else empty

typeconstraint (SumValue mts (t, e)) = do
    types <- mapM (\(s, mt) -> do
        vari <- lift $ lift get
        lift $ lift $ put $ vari + 1
        let t' = fromMaybe (TypeVar vari) mt
        return (s, t')) mts
    (t2, ce) <- typeconstraint e
    return (Sum ((t, t2):types), SumValue (map (second Just) types) (t, ce))

typeconstraint (CaseOfSum e exps) = do
    (st, ce) <- typeconstraint e
    (bctx, fctx) <- get
    inferredexps <- mapM (\(s, ex) -> do
        vari <- lift $ lift get
        let tv = TypeVar vari
        lift $ lift $ put $ vari + 1
        put (Just tv:bctx, fctx)
        (t', ce) <- typeconstraint ex
        ctx' <- get
        return (t', s, ce, ctx')
        ) exps
    -- TODO: Probably doable in a more idiomatic way, like making an inference monad instead of all these function parameters
    let (t1', s1, ce1, ctx1') = head inferredexps
    if all ((== ctx1') . (\(_,_,_,c) -> c)) (tail inferredexps)
       then writer ((t1', CaseOfSum ce (map (\(_,s,c,_) -> (s,c)) inferredexps)), Constraint st (Sum (map (\(t,s,_,_) -> (s, t)) inferredexps)):map (\(t'',_,_,_) -> Constraint t1' t'') (tail inferredexps))
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
    ((ctype, cexp), constraints) <- evalStateT (evalStateT (runWriterT $ typeconstraint e) ([], fc)) (length fc)
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


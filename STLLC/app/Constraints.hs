{-# LANGUAGE LambdaCase #-}
module Constraints (Constraint(..), Subst(..), Substitutable(..), ftv, solveconstraints, solveconstraintsExistential, compose, unifyExistential) where

import Data.List (sortBy)
import Data.Bifunctor (second)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Debug.Trace
import Control.Monad
import Data.Maybe


import CoreSyntax
import qualified Syntax



-------------------------------------------------------------------------------
-- Datatypes
-------------------------------------------------------------------------------

data Constraint = Constraint Type Type deriving (Eq) -- e.g. [X => Y]


type Subst = Map.Map Int Type





-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

---- * Show * ----

instance Show Constraint where
    show (Constraint t t') = "[" ++ show t ++ " => " ++ show t' ++ "]"


---- * Substitutable * -----

class Substitutable a where
    apply :: Subst -> a -> a


instance Substitutable Scheme where
    apply s (Forall ns t) = Forall ns $ apply s' t 
                            where s' = foldr Map.delete s ns 


instance Substitutable Type where
    apply s (Fun t1 t2) = Fun (apply s t1) (apply s t2)
    apply s (Tensor t1 t2) = Tensor (apply s t1) (apply s t2)
    apply s (With t1 t2) = With (apply s t1) (apply s t2)
    apply s (Plus t1 t2) = Plus (apply s t1) (apply s t2)
    apply s (Bang t) = Bang (apply s t)
    apply s t@(TypeVar i) = Map.findWithDefault t i s
    apply s t@(ExistentialTypeVar i) = Map.findWithDefault t (-i) s
    apply s (Sum tl) = Sum $ map (second $ apply s) tl
    apply s (ADT n tp) = ADT n $ map (apply s) tp
    apply s t@(RefinementType n tp ls p) =
        RefinementType n (apply s tp) (apply s ls) p
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
    apply s (Mark i n ctx (Just t)) = Mark i n (apply s ctx) (return $ apply s t)
    apply s (SumValue tl (i, e)) = SumValue (map (second $ apply s) tl) (i, apply s e)
    apply s (CaseOfSum e el) = CaseOfSum (apply s e) (map (second $ apply s) el)
    apply s (CaseOf e el) = CaseOf (apply s e) (map (second $ apply s) el)
    apply s e = e


instance Substitutable CoreSyntax.Var where
    apply s (CoreSyntax.Var m sch) = Var m $ apply s sch


instance Substitutable CoreBinding where
    apply s (CoreBinding n e') = CoreBinding n (apply s e')


instance Substitutable Char where
    apply s c = c


instance Substitutable a => Substitutable (Maybe a) where
    apply s Nothing = Nothing
    apply s (Just t) = Just (apply s t)


instance Substitutable a => Substitutable [a] where
    apply s l = map (apply s) l


instance (Substitutable a, Substitutable b) => Substitutable ((,) a b) where
    apply s (x, y) = (apply s x, apply s y)


instance Substitutable Constraint where
    apply s (Constraint t1 t2) = Constraint (apply s t1) (apply s t2)






-------------------------------------------------------------------------------
-- Functions
-------------------------------------------------------------------------------

unify :: Type -> Type -> Maybe Subst 
unify Unit Unit = Just Map.empty
unify (TyLit x) (TyLit y) = if x == y then Just Map.empty else Nothing
unify (ADT x ts) (ADT y ts') =
    if x == y
       then do
           guard $ length ts == length ts'
           let maybesubs = zipWith unify ts ts'
           foldM (\p n -> compose p <$> n) Map.empty maybesubs
       else Nothing
unify (TypeVar x) (TypeVar y) = if x == y then Just Map.empty else Just $ Map.singleton x (TypeVar y)
unify (TypeVar x) y = if x `notElem` ftv y then Just $ Map.singleton x y else Nothing
unify x (TypeVar y) = if y `notElem` ftv x then Just $ Map.singleton y x else Nothing
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
unify a@(RefinementType n x _ _) (RefinementType n' y _ _) = do -- TODO: ? Unify later refinement types, just make sure the types align for now
    unify x y
unify (RefinementType _ x _ _) y = unify x y
unify x (RefinementType _ y _ _) = unify x y 
unify (Sum xtl) (Sum ytl) = do
    let xtl' = sortBy (\(a,_) (b,_) -> compare a b) xtl
    let ytl' = sortBy (\(a,_) (b,_) -> compare a b) ytl
    let maybesubs = zipWith (\x y -> snd x `unify` snd y) xtl' ytl'
    foldM (\p n -> compose p <$> n) Map.empty maybesubs
unify _ _ = Nothing


unifyExistential :: Type -> Type -> Maybe Subst 
unifyExistential Unit Unit = Just Map.empty
unifyExistential (TyLit x) (TyLit y) = if x == y then Just Map.empty else Nothing
unifyExistential (ADT x ts) (ADT y ts') =
    if x == y
       then do
           guard $ length ts == length ts'
           let maybesubs = zipWith unifyExistential ts ts'
           foldM (\p n -> compose p <$> n) Map.empty maybesubs
       else Nothing
unifyExistential (TypeVar x) (TypeVar y) = if x == y then Just Map.empty else Nothing
unifyExistential (ExistentialTypeVar x) (ExistentialTypeVar y) = if x == y then Just Map.empty else Just $ Map.singleton x (ExistentialTypeVar y)
unifyExistential (ExistentialTypeVar x) y =
    if (-x) `notElem` ftv y then Just $ Map.singleton (-x) y else Nothing
unifyExistential x (ExistentialTypeVar y) =
    if (-y) `notElem` ftv x then Just $ Map.singleton (-y) x else Nothing
unifyExistential (Fun t1 t2) (Fun t1' t2') = do
    s  <- unifyExistential t1 t1'
    s' <- unifyExistential (apply s t2) (apply s t2')
    return $ compose s' s
unifyExistential (Tensor t1 t2) (Tensor t1' t2') = do
    s  <- unifyExistential t1 t1'
    s' <- unifyExistential (apply s t2) (apply s t2')
    return $ compose s' s
unifyExistential (With t1 t2) (With t1' t2') = do
    s  <- unifyExistential t1 t1'
    s' <- unifyExistential (apply s t2) (apply s t2')
    return $ compose s' s
unifyExistential (Plus t1 t2) (Plus t1' t2') = do
    s  <- unifyExistential t1 t1'
    s' <- unifyExistential (apply s t2) (apply s t2')
    return $ compose s' s
unifyExistential (Bang x) (Bang y) = unifyExistential x y
unifyExistential (Sum xtl) (Sum ytl) = do
    let xtl' = sortBy (\(a,_) (b,_) -> compare a b) xtl
    let ytl' = sortBy (\(a,_) (b,_) -> compare a b) ytl
    let maybesubs = zipWith (\x y -> snd x `unifyExistential` snd y) xtl' ytl'
    foldM (\p n -> compose p <$> n) Map.empty maybesubs
unifyExistential _ _ = Nothing


compose :: Subst -> Subst -> Subst
s' `compose` s = Map.map (apply s') s `Map.union` s'





-------------------------------------------------------------------------------
-- Exported Functions
-------------------------------------------------------------------------------

ftv :: Type -> Set.Set Int
ftv (Fun t t') = ftv t `Set.union` ftv t'
ftv (Tensor t t') = ftv t `Set.union` ftv t'
ftv (With t t') = ftv t `Set.union` ftv t'
ftv (Plus t t') = ftv t `Set.union` ftv t'
ftv (Bang t) = ftv t
ftv (TypeVar x) = Set.singleton x 
ftv (ExistentialTypeVar x) = Set.singleton (-x) 
ftv (Sum []) = Set.empty
ftv (Sum ((i, t):ts)) = ftv t `Set.union` ftv (Sum ts)
ftv (ADT _ ts) = foldr (Set.union . ftv ) Set.empty ts
ftv (RefinementType _ x _ _) = ftv x -- TODO: possibly missing free variables from refinement context?
ftv t = Set.empty


solveconstraints :: Subst -> [Constraint] -> Maybe Subst -- w/ substitution accumulator and list of constraints generate a substitution
solveconstraints subs constr =
    case constr of
      [] -> return subs
      Constraint t1 t2:cs -> do
          case unify t1 t2 of
            Nothing -> error ("Failed to unify " ++ show t1 ++ " with " ++ show t2)
            Just s -> solveconstraints (compose s subs) $ map (apply s) cs


solveconstraintsExistential :: Subst -> Constraint -> Maybe Subst
solveconstraintsExistential subs c = solveconstraintsExistential' Map.empty (c : map (\(k,v) -> Constraint (ExistentialTypeVar (-k)) v) (Map.toList subs))
    where
        solveconstraintsExistential' :: Subst -> [Constraint] -> Maybe Subst
        solveconstraintsExistential' subs constraints =
            case constraints of
              [] -> return subs
              Constraint t1 t2:cs -> do
                s <- unifyExistential t1 t2
                solveconstraintsExistential' (compose s subs) $ map (apply s) cs


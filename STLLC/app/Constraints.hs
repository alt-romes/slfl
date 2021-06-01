module Constraints where

import Data.Bifunctor (second)
import Data.Maybe
import Data.List (sortBy)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad

import CoreSyntax

type Ctxt = ([Maybe Scheme], [(String, Scheme)])

data Constraint = Constraint Type Type -- e.g. [X => Y]
instance Show Constraint where
    show (Constraint t t') = "[" ++ show t ++ " => " ++ show t' ++ "]"

type Subst = Map.Map Int Type

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


ftv :: Type -> Set.Set Int
ftv = ftv' Set.empty
    where
        ftv' :: Set.Set Int -> Type -> Set.Set Int
        ftv' acc (Fun t t') = ftv' acc t `mappend` ftv' acc t'
        ftv' acc (Tensor t t') = ftv' acc t `mappend` ftv' acc t'
        ftv' acc (With t t') = ftv' acc t `mappend` ftv' acc t'
        ftv' acc (Plus t t') = ftv' acc t `mappend` ftv' acc t'
        ftv' acc (Bang t) = ftv' acc t
        ftv' acc (TypeVar x) = Set.insert x acc
        ftv' acc (Sum []) = acc
        ftv' acc (Sum ((i, t):ts)) = ftv' acc t `mappend` ftv' acc (Sum ts)
        ftv' acc t = acc

ftvctx :: Ctxt -> Set.Set Int
ftvctx = ftvctx' Set.empty
    where
        ftvctx' :: Set.Set Int -> Ctxt -> Set.Set Int
        ftvctx' acc (bc, fc) = Set.unions (map ftvsch (catMaybes bc)) `Set.union` Set.unions (map (ftvsch . snd) fc)
        ftvsch (Forall ns t) = Set.difference (Set.fromList ns) $ ftv t

unify :: Type -> Type -> Maybe Subst 
unify Bool Bool = Just Map.empty
unify (Atom x) (Atom y) = if x == y then Just Map.empty else Nothing
unify Unit Unit = Just Map.empty
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
unify (Sum xtl) (Sum ytl) = do
    let xtl' = sortBy (\(a,_) (b,_) -> compare a b) xtl
    let ytl' = sortBy (\(a,_) (b,_) -> compare a b) ytl
    let maybesubs = zipWith (\x y -> snd x `unify` snd y) xtl' ytl'
    foldM (\p n -> compose p <$> n) Map.empty maybesubs
unify _ _ = Nothing

compose :: Subst -> Subst -> Subst
s' `compose` s = Map.map (apply s') s `Map.union` s'

solveconstraints :: Subst -> [Constraint] -> Maybe Subst -- w/ substitution accumulator and list of constraints generate a substitution
solveconstraints subs constr =
    case constr of
      [] -> return subs
      Constraint t1 t2:cs -> do
          s <- unify t1 t2
          solveconstraints (compose s subs) $ map (\(Constraint t1 t2) -> Constraint (apply s t1) (apply s t2)) cs

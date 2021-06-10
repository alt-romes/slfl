module CoreSyntax (CoreExpr(..), Type(..), Scheme(..), Name, CoreBinding(..), transformM, transform) where 

import Prelude hiding (Bool)
import Control.Monad
import Data.Maybe
import Data.Bifunctor
import Data.Functor.Identity



type Name = String

-------------------------------------------------------------------------------
-- Datatypes
-------------------------------------------------------------------------------

data CoreBinding = CoreBinding Name CoreExpr


data CoreExpr

    = BLVar Int             -- bound linear/restricted var
    | BUVar Int             -- bound unrestricted var
    | FLVar String          -- free linear/restricted var
    | FUVar String          -- free unrestricted var

    -- A -o B
    | Abs (Maybe Type) CoreExpr     -- \x:T -> M . with Bruijn indices
    | App CoreExpr CoreExpr -- M N

    -- A (*) B
    | TensorValue CoreExpr CoreExpr
    | LetTensor CoreExpr CoreExpr

    -- 1
    | UnitValue
    | LetUnit CoreExpr CoreExpr

    -- A & B
    | WithValue CoreExpr CoreExpr
    | Fst CoreExpr
    | Snd CoreExpr

    -- A (+) B
    | InjL (Maybe Type) CoreExpr    -- inr A : M has type A (+) typeof M
    | InjR (Maybe Type) CoreExpr    -- inl M : B has type typeof M (+) A
    | CaseOfPlus CoreExpr CoreExpr CoreExpr -- case M of inl x => N | inr y => P : C

    -- !A
    | BangValue CoreExpr
    | LetBang CoreExpr CoreExpr

    -- Non-canonical

    | LetIn CoreExpr CoreExpr

    | Mark Int [(String, Scheme)] (Maybe Type)

    -- Sum types
    | SumValue [(String, Maybe Type)] (String, CoreExpr)
    | CaseOfSum CoreExpr [(String, CoreExpr)]
  
    | CaseOf CoreExpr [(String, CoreExpr)]

    deriving (Eq)


data Scheme = Forall [Int] Type deriving (Eq)


data Type
    = Fun Type Type     -- A -o B 
    | Tensor Type Type  -- A * B    -- multiplicative conjunction
    | Unit              -- 1
    | With Type Type    -- A & B    -- additive conjuntion
    | Plus Type Type    -- A + B    -- additive disjunction
    | Bang Type         -- !A       -- exponential

    | TypeVar Int       -- Type variable (uninterpreted type) used for reconstruction
    | ExistentialTypeVar Int

    | Sum [(String, Type)]

    | ADT String
    
    deriving (Eq)





-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

---- * Show * ----

instance (Show CoreBinding) where
    show (CoreBinding s e) = s ++ ":\n" ++ show e ++ "\n"


instance (Show CoreExpr) where
    show e = showexpr' 0 e


instance (Show Scheme) where
    show (Forall ns t) = (if null ns then "" else foldl (\p n -> p ++ " " ++ (letters !! n)) "forall" ns ++ ". ") ++ show t


instance (Show Type) where 
    show (Fun t1 t2) = "(" ++ show t1 ++ " -o " ++ show t2 ++ ")"
    show (Tensor t1 t2) = "(" ++ show t1 ++ " * " ++ show t2 ++ ")"
    show Unit = "1"
    show (With t1 t2) = "(" ++ show t1 ++ " & " ++ show t2 ++ ")"
    show (Plus t1 t2) = "(" ++ show t1 ++ " + " ++ show t2 ++ ")"
    show (Bang t1) = "(! " ++ show t1 ++ ")"
    show (TypeVar x) = letters !! x
    show (ExistentialTypeVar x) = "?" ++ letters !! x
    show (Sum ts) = "+ { " ++ foldl (\p (s, t) -> p ++ s ++ " : " ++ show t ++ "; ") "" ts ++ "}"
    show (ADT t) = t





-------------------------------------------------------------------------------
-- Traversal
-------------------------------------------------------------------------------

transformM :: (Monad m, Applicative m) => (CoreExpr -> m CoreExpr) -> CoreExpr -> m CoreExpr
transformM f (BLVar x) = f $ BLVar x
transformM f (BUVar x) = f $ BUVar x
transformM f (FLVar x) = f $ FLVar x
transformM f (FUVar x) = f $ FUVar x
transformM f (Abs t e) = f . Abs t =<< transformM f e
transformM f (App e1 e2) = f =<< (App <$> transformM f e1 <*> transformM f e2)
transformM f (TensorValue e1 e2) = f =<< (TensorValue <$> transformM f e1 <*> transformM f e2)
transformM f (LetTensor e1 e2) = f =<< (LetTensor <$> transformM f e1 <*> transformM f e2)
transformM f UnitValue = f UnitValue
transformM f (LetUnit e1 e2) = f =<< (LetUnit <$> transformM f e1 <*> transformM f e2)
transformM f (WithValue e1 e2) = f =<< (WithValue <$> transformM f e1 <*> transformM f e2)
transformM f (Fst e) = f . Fst =<< transformM f e
transformM f (Snd e) = f . Snd =<< transformM f e
transformM f (InjL t e) = f . InjL t =<< transformM f e
transformM f (InjR t e) = f . InjR t =<< transformM f e
transformM f (CaseOfPlus e1 e2 e3) = f =<< (CaseOfPlus <$> transformM f e1 <*> transformM f e2 <*> transformM f e3)
transformM f (BangValue e) = f . BangValue =<< transformM f e
transformM f (LetBang e1 e2) = f =<< (LetBang <$> transformM f e1 <*> transformM f e2)
transformM f (LetIn e1 e2) = f =<< (LetIn <$> transformM f e1 <*> transformM f e2)
transformM f (Mark a b t) = f $ Mark a b t
transformM f (SumValue mts (s, e)) = f . SumValue mts . (,) s =<< transformM f e
transformM f (CaseOfSum e ls) = f =<< (CaseOfSum <$> transformM f e <*> traverse (\ (s, e) -> (,) s <$> transformM f e) ls)
transformM f (CaseOf e ls) = f =<< (CaseOf <$> transformM f e <*> traverse (\ (s, e) -> (,) s <$> transformM f e) ls)


transform :: (CoreExpr -> CoreExpr) -> CoreExpr -> CoreExpr
transform f e = runIdentity (transformM (return . f) e)





-------------------------------------------------------------------------------
-- Util
-------------------------------------------------------------------------------

showexpr' :: Int -> CoreExpr -> String -- Use Int (depth) to indent the code
showexpr' _ (BLVar x) = "BL(" ++ show x ++ ")"
showexpr' _ (BUVar x) = "BU(" ++ show x ++ ")"
showexpr' _ (FLVar x) = "FL(" ++ show x ++ ")"
showexpr' _ (FUVar x) = "FU(" ++ show x ++ ")"
showexpr' d (Abs t e) = indent d ++ "(λ" ++ " : " ++ show t ++ " -> " ++ showexpr' (d+1) e ++ ")"
showexpr' d (App e1 e2) = showexpr' d e1 ++ " " ++ showexpr' d e2
showexpr' d (TensorValue e1 e2) = "< " ++ showexpr' d e1 ++ " * " ++ showexpr' d e2 ++ " >"
showexpr' d (LetTensor e1 e2) = indent d ++ "let " ++ "?" ++ "*" ++ "?" ++ " = " ++ showexpr' d e1 ++ " in " ++ showexpr' (d+1) e2
showexpr' _ UnitValue = "<>"
showexpr' d (LetUnit e1 e2) = indent d ++ "let _ = " ++ showexpr' d e1 ++ " in " ++ showexpr' (d+1) e2
showexpr' d (WithValue e1 e2) = "< " ++ showexpr' d e1 ++ " & " ++ showexpr' d e2 ++ " >"
showexpr' d (Fst a@(App _ _)) = "fst (" ++ showexpr' d a ++ ")"
showexpr' d (Snd a@(App _ _)) = "snd (" ++ showexpr' d a ++ ")"
showexpr' d (Fst e) = "fst " ++ showexpr' d e
showexpr' d (Snd e) = "snd " ++ showexpr' d e
showexpr' d (InjL t e) = "inl " ++ showexpr' d e ++ " : " ++ show t
showexpr' d (InjR t e) = "inr " ++ show t ++ " : " ++ showexpr' d e
showexpr' d (CaseOfPlus e1 e2 e3) = indent d ++ "case " ++ showexpr' d e1 ++ " of " ++
                                            indent (d+1) ++ "inl " ++ "?" ++ " => " ++ showexpr' (d+2) e2 ++
                                            indent (d+1) ++ "| inr " ++ "?" ++ " => " ++ showexpr' (d+2) e3
showexpr' d (BangValue e) = "! " ++ showexpr' d e ++ ""
showexpr' d (LetBang e1 e2) = indent d ++ "let !" ++ "?" ++ " = " ++ showexpr' d e1 ++ " in " ++ showexpr' (d+1) e2
showexpr' d (LetIn e1 e2) = indent d ++ "let " ++ "?" ++ " = " ++ showexpr' d e1 ++ " in " ++ showexpr' (d+1) e2
showexpr' _ (Mark _ _ t) = "{{ " ++ show t ++ " }}"
showexpr' d (SumValue mts (s, e)) = indent d ++ "union {" ++
    foldl (\p (s', t) -> p ++ indent (d+2) ++ s' ++ " : " ++ show (fromJust t) ++ ";") "" mts
    ++ indent (d+2) ++ s ++ " " ++ show e ++ ";"
    ++ indent (d+1) ++ "}"
showexpr' _ (CaseOfSum _ []) = error "Case of sum should have at least one tag"
showexpr' d (CaseOfSum e ((tag, e1):exps)) = indent d ++ "case " ++ showexpr' d e ++ " of " ++
    indent (d+1) ++ "  " ++ tag ++ " " ++ "?" ++ " => " ++ showexpr' (d+2) e1 ++
        foldl (\p (t, ex) -> p ++ indent (d+1) ++ 
            "| " ++ t ++ " " ++ "?" ++ " => " ++
                showexpr' (d+2) ex) "" exps
showexpr' _ (CaseOf _ []) = error "Case of sum should have at least one tag"
showexpr' d (CaseOf e ((tag, e1):exps)) = indent d ++ "case " ++ showexpr' d e ++ " of " ++
    indent (d+1) ++ "  " ++ tag ++ " " ++ "?" ++ " => " ++ showexpr' (d+2) e1 ++
        foldl (\p (t, ex) -> p ++ indent (d+1) ++ 
            "| " ++ t ++ " " ++ "?" ++ " => " ++
                showexpr' (d+2) ex) "" exps


indent :: Int -> String
indent d = (if d == 0 then "" else "\n") ++ replicate (4*d) ' '


letters :: [String]
letters = [1..] >>= flip replicateM ['a'..'z']


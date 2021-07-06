{-# LANGUAGE LambdaCase #-}
module CoreSyntax (CoreExpr(..), Type(..), Scheme(..), Name, CoreBinding(..),
    TypeBinding(..), Var(..), Mult(..), transformM, transform, trivialScheme,
    Literal(..), TyLiteral(..), isInType, trivialInt,
    isExistentialType, Predicate(..), trivialIntRefinement, isInt) where 

import Control.Monad
import Data.Maybe
import Data.Hashable
import Control.Applicative
import Data.Bifunctor
import Data.Functor.Identity


import Util



type Name = String

-------------------------------------------------------------------------------
-- Datatypes
-------------------------------------------------------------------------------

data CoreBinding = CoreBinding Name CoreExpr


data TypeBinding = TypeBinding String Scheme deriving (Eq)


data CoreExpr

    = Lit Literal
    | BLVar Int             -- bound linear/restricted var
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

    | Mark Int (Maybe Name) ([Maybe Var], [(String, Scheme)]) (Maybe Scheme) -- TODO: Once again assuming we can't have free linear variables

    -- Sum types
    | SumValue [(String, Maybe Type)] (String, CoreExpr)
    | CaseOfSum CoreExpr [(String, CoreExpr)]
  
    | CaseOf CoreExpr [(String, CoreExpr)]

    deriving (Eq)


newtype Literal = LitInt Integer deriving (Eq, Ord)



data Var = Var
    { varMult :: Mult 
    , unVar   :: Scheme
    } deriving (Eq, Show, Ord)
data Mult = Lin | Unr deriving (Eq, Show, Ord)


data Scheme = Forall [Int] Type deriving (Eq, Ord)


data Type
    = TyLit TyLiteral
    | Fun Type Type     -- A -o B 
    | Tensor Type Type  -- A * B    -- multiplicative conjunction
    | Unit              -- 1
    | With Type Type    -- A & B    -- additive conjuntion
    | Plus Type Type    -- A + B    -- additive disjunction
    | Bang Type         -- !A       -- exponential

    | TypeVar Int       -- Type variable (uninterpreted type) used for reconstruction
    | ExistentialTypeVar Int

    | Sum [(Name, Type)]

    | ADT Name [Type]

    | RefinementType Name Type [Type] (Maybe Predicate)
    
    deriving (Eq, Ord)

data TyLiteral = TyInt deriving (Eq, Ord)

data Predicate
    = PVar Name
    | PBool Bool
    | PNum Integer
    | Conjunction Predicate Predicate
    | Disjunction Predicate Predicate
    | Negation Predicate
    | Conditional Predicate Predicate Predicate
    | UnaryOp Name Predicate
    | BinaryOp Name Predicate Predicate
    deriving (Eq, Ord)





-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

---- * Show * ----

instance (Show CoreBinding) where
    show (CoreBinding s e) = s ++ ":\n" ++ show e ++ ";\n"


instance (Show TypeBinding) where
    show (TypeBinding s sch) = s ++ " :: " ++ show sch ++ ";\n"


instance (Show CoreExpr) where
    show e = showexpr' 0 e


instance (Show Type) where 
    show (TyLit l) = show l
    show (Fun t1 t2) = "(" ++ show t1 ++ " -> " ++ show t2 ++ ")"
    show (Tensor t1 t2) = "(" ++ show t1 ++ " * " ++ show t2 ++ ")"
    show Unit = "1"
    show (With t1 t2) = "(" ++ show t1 ++ " & " ++ show t2 ++ ")"
    show (Plus t1 t2) = "(" ++ show t1 ++ " + " ++ show t2 ++ ")"
    show (Bang t1) = "!" ++ show t1
    show (TypeVar x) = getName x
    show (ExistentialTypeVar x) = "?" ++ getName x
    show (Sum ts) = "+ { " ++ foldl (\p (s, t) -> p ++ s ++ " : " ++ show t ++ "; ") "" ts ++ "}"
    show (ADT n ts) = n ++ concatMap ((" " ++) . (\case t@ADT {} -> "(" ++ show t ++ ")"; t -> show t)) ts
    show (RefinementType n t _ Nothing) = n ++ " { " ++ show t ++ " }"
    show (RefinementType n t l (Just p)) = n ++ " { " ++ show t ++ " | " ++ show p ++ " }" ++ " com " ++ show l


instance (Show Scheme) where
    show (Forall ns t) = (if null ns then "" else foldl (\p n -> p ++ " " ++ (letters !! n)) "forall" ns ++ " . ") ++ show t


instance (Show Literal) where
    show (LitInt x) = show x


instance (Show TyLiteral) where
    show TyInt = "Int"


instance Show Predicate where
    show (PVar n) = n
    show (PNum n) = show n
    show (UnaryOp n p) = n ++ show p
    show (BinaryOp n p1 p2) = "(" ++ show p1 ++ " " ++ n ++ " " ++ show p2 ++ ")"
    show (Conjunction p1 p2) = show p1 ++ " ^ " ++ show p2


instance Hashable Scheme where
    hashWithSalt a (Forall ns t) = foldl ((+) . hashWithSalt (a-100)) 0 ns + hashWithSalt (a-200) t


instance Hashable Type where
    hashWithSalt a t = case t of
        Unit -> hashWithSalt (a+10) "Unit"
        TyLit l -> hashWithSalt a l
        Fun t1 t2 -> hashWithSalt (a+2000) t1 + hashWithSalt (a+2000) t2
        Tensor t1 t2 -> hashWithSalt (a+3000) t1 + hashWithSalt (a+3000) t2
        With t1 t2 -> hashWithSalt (a+4000) t1 + hashWithSalt (a+4000) t2
        Plus t1 t2 -> hashWithSalt (a+5000) t1 + hashWithSalt (a+5000) t2
        Bang t -> hashWithSalt (a+6000) t
        TypeVar x -> hashWithSalt (a+7000) x
        ExistentialTypeVar x -> hashWithSalt (a+8000) x
        Sum ts -> sum $ map (hashWithSalt (a+9000)) ts
        ADT tyn tps -> hashWithSalt (a+1000) tyn + sum (map (hashWithSalt (a+1000)) tps)
        RefinementType n tp ls p -> hashWithSalt (a+20000) n + hashWithSalt (a+2000) tp + hashWithSalt (a+20000) ls
        -- x -> error ("Hashing unknown type " ++ show x)


instance Hashable TyLiteral where
    hashWithSalt a TyInt = hashWithSalt (a+10) "TyInt"




-------------------------------------------------------------------------------
-- Traversal
-------------------------------------------------------------------------------

transformM :: (Monad m, Applicative m) => (CoreExpr -> m CoreExpr) -> CoreExpr -> m CoreExpr
transformM f (Lit x) = f $ Lit x
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
transformM f (Mark a n b t) = f $ Mark a n b t
transformM f (SumValue mts (s, e)) = f . SumValue mts . (,) s =<< transformM f e
transformM f (CaseOfSum e ls) = f =<< (CaseOfSum <$> transformM f e <*> traverse (\ (s, e) -> (,) s <$> transformM f e) ls)
transformM f (CaseOf e ls) = f =<< (CaseOf <$> transformM f e <*> traverse (\ (s, e) -> (,) s <$> transformM f e) ls)


transform :: (CoreExpr -> CoreExpr) -> CoreExpr -> CoreExpr
transform f e = runIdentity (transformM (return . f) e)





-------------------------------------------------------------------------------
-- Functions
-------------------------------------------------------------------------------

-- pre: No free tvars in t
trivialScheme :: Type -> Scheme 
trivialScheme = Forall []

trivialInt :: Type
trivialInt = TyLit TyInt

isInt :: Type -> Bool
isInt t = case t of
            TyLit TyInt -> True
            _ -> False

trivialRefinement :: Name -> Type -> Type
trivialRefinement n t = RefinementType n t [] Nothing

trivialIntRefinement :: Name -> Type
trivialIntRefinement n = RefinementType n trivialInt [] Nothing


isInType :: Type -> Type -> Bool
isInType t1 t2 =
    case t2 of
      Fun t1' t2' -> isInType t1 t1' || isInType t1 t2'
      Tensor t1' t2' -> isInType t1 t1' || isInType t1 t2'
      With t1' t2' -> isInType t1 t1' || isInType t1 t2'
      Plus t1' t2' -> isInType t1 t1' || isInType t1 t2'
      Bang t' -> isInType t1 t'
      _ -> t1 == t2


isExistentialType :: Type -> Bool
isExistentialType (ExistentialTypeVar _) = True
isExistentialType (Fun t1 t2) = isExistentialType t1 || isExistentialType t2
isExistentialType (Tensor t1 t2) = isExistentialType t1 || isExistentialType t2
isExistentialType (With t1 t2) = isExistentialType t1 || isExistentialType t2
isExistentialType (Plus t1 t2) = isExistentialType t1 || isExistentialType t2
isExistentialType (Bang t1) = isExistentialType t1
isExistentialType (Sum ts) = any (isExistentialType . snd) ts
isExistentialType (ADT n ts) = any isExistentialType ts
isExistentialType (TyLit l) = False
isExistentialType (TypeVar x) = False
isExistentialType (RefinementType _ t _ _) = isExistentialType t
isExistentialType Unit = False





-------------------------------------------------------------------------------
-- Util
-------------------------------------------------------------------------------

showexpr' :: Int -> CoreExpr -> String -- Use Int (depth) to indent the code
showexpr' _ (Lit x) = "Lit(" ++ show x ++ ")"
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
showexpr' _ (Mark i n c t) = "{{ " ++ show i ++ " : " ++ show t ++ " in context" ++ show c ++ " }}"
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


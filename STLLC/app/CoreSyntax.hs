{-# LANGUAGE LambdaCase, DeriveGeneric, DeriveAnyClass, OverloadedStrings #-}
module CoreSyntax (CoreExpr(..), Type(..), Scheme(..), Name, CoreBinding(..),
    TypeBinding(..), Var(..), Mult(..), transformM, transform, trivialScheme,
    Literal(..), TyLiteral(..), isInType, trivialInt, isExistentialType,
    Predicate(..), trivialIntRefinement, isInt, isADTBool, transformTypeM,
    transformType, isFunction) where 

import Prelude hiding ((<>))
import Control.Monad
import Control.Monad.State
import Data.Maybe
import Data.Hashable
import Control.Applicative
import GHC.Generics (Generic)
import Control.DeepSeq
import Data.Bifunctor
import Text.PrettyPrint as P
import Data.Functor.Identity


import Util



type Name = String

-------------------------------------------------------------------------------
-- Datatypes
-------------------------------------------------------------------------------

data CoreBinding = CoreBinding Name CoreExpr


data TypeBinding = TypeBinding Name Scheme deriving (Eq)


data CoreExpr

    = Lit Literal
    | BLVar Int             -- bound linear/restricted var
    | BUVar Int             -- bound unrestricted var
    | FLVar Name          -- free linear/restricted var
    | FUVar Name          -- free unrestricted var

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

    | Mark Int (Maybe Name) ([Maybe Var], [(String, Scheme)]) (Maybe Scheme) (Int, [Name], Int) -- TODO: Once again assuming we can't have free linear variables

    -- Sum types
    | SumValue [(Name, Maybe Type)] (Name, CoreExpr)
    | CaseOfSum CoreExpr [(Name, CoreExpr)]
  
    | CaseOf CoreExpr [(Name, CoreExpr)]

    | ADTVal Name (Maybe CoreExpr)
    
    deriving (Eq)


newtype Literal = LitInt Integer deriving (Eq, Ord, Generic, NFData)



data Var = Var
    { varMult :: Mult 
    , unVar   :: Scheme
    } deriving (Eq, Show, Ord)
data Mult = Lin | Unr deriving (Eq, Show, Ord, Generic, NFData)


data Scheme = Forall [Int] Type deriving (Eq, Ord, Generic, NFData)


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

    deriving (Eq, Ord, Generic, NFData)

data TyLiteral = TyInt deriving (Eq, Ord, Generic, NFData)

data Predicate
    = PVar Name
    | PBool Bool
    | PNum Integer
    | Conditional Predicate Predicate Predicate
    | UnaryOp Name Predicate
    | BinaryOp Name Predicate Predicate
    deriving (Eq, Ord, Generic, NFData)





-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

---- * Show * ----

instance (Show CoreBinding) where
    show (CoreBinding s e) = s ++ ":\n" ++ show e ++ ";\n"


instance (Show TypeBinding) where
    show (TypeBinding s sch) = s ++ " :: " ++ show sch ++ ";\n"


instance (Show CoreExpr) where
    show = render . ppr 0


instance (Show Type) where 
    show = render . ppr 0


instance (Show Scheme) where
    show (Forall ns t) = (if null ns then "" else foldl (\p n -> p ++ " " ++ (letters !! n)) "forall" ns ++ " . ") ++ show t


instance (Show Literal) where
    show (LitInt x) = show x


instance (Show TyLiteral) where
    show TyInt = "Int"


instance Show Predicate where
    show = render . ppr 0


instance Hashable Scheme where
    hashWithSalt a (Forall ns t) = foldl ((+) . hashWithSalt (a-100)) 0 ns + hashWithSalt (a-200) t


instance Hashable Type where
    hashWithSalt a t = case t of
        Unit -> hashWithSalt (a+10) ("Unit" :: String)
        TyLit l -> hashWithSalt a l
        Fun t1 t2 -> hashWithSalt (a+2000) t1 + hashWithSalt (a+2000) t2
        Tensor t1 t2 -> hashWithSalt (a+3000) t1 + hashWithSalt (a+3000) t2
        With t1 t2 -> hashWithSalt (a+4000) t1 + hashWithSalt (a+4000) t2
        Plus t1 t2 -> hashWithSalt (a+5000) t1 + hashWithSalt (a+5000) t2
        Bang t -> hashWithSalt (a+6000) t
        TypeVar x -> hashWithSalt (a+7000) x
        ExistentialTypeVar x -> hash ("?:)" :: String) -- hashWithSalt (a+8000) x
        Sum ts -> sum $ map (hashWithSalt (a+9000)) ts
        ADT tyn tps -> hashWithSalt (a+1000) tyn + sum (map (hashWithSalt (a+1000)) tps)
        RefinementType n tp ls p -> hashWithSalt (a+20000) n + hashWithSalt (a+2000) tp + hashWithSalt (a+20000) ls
        -- x -> error ("Hashing unknown type " ++ show x)


instance Hashable TyLiteral where
    hashWithSalt a TyInt = hashWithSalt (a+10) ("TyInt" :: String)

instance Pretty Type where
    ppr p t = case t of
        TyLit l -> text $ show l
        Fun t1 t2 -> parens (pp t1 <+> "-o" <+> pp t2)
        Tensor t1 t2 -> parens (pp t1 <+> char '*' <+> pp t2)
        Unit -> char '1'
        With t1 t2 -> parens (pp t1 <+> char '&' <+> pp t2)
        Plus t1 t2 -> parens (pp t1 <+> char '+' <+> pp t2)
        Bang t -> parens (char '!' <+> pp t)
        TypeVar x -> text $ letters !! x
        ExistentialTypeVar x -> char '?' <> text (letters !! x)
        Sum ts -> "+ {" <+> foldl (\p (s, t) -> p <> text s <+> ":" <+> pp t <> "; ") "" ts <> "}"
        ADT n ts -> text n <+> foldl (\p -> \case t@ADT {} -> p <+> "(" <> pp t <> ")"; t -> p <+> pp t) "" ts
        RefinementType n t _ Nothing -> text n <+> "{" <+> pp t <+> "}"
        RefinementType n t l (Just p) -> text n <+> "{" <+> pp t <+> "|" <+> foldr (\(RefinementType _ _ _ mp) -> ((case mp of {Nothing -> ""; Just p' -> pp p' <+> "=>"}) <+>)) "" l <+> pp p <+> "}"


instance Pretty Literal where
    ppr p (LitInt i) = integer i


instance Pretty Scheme where
    ppr p (Forall ns t) = (if null ns then P.empty else foldl (\p n -> p <+> text (letters !! n)) "forall" ns <+> ".") <> pp t


instance Pretty Predicate where
    ppr i p = case p of
        PVar n -> text n
        PNum n -> text $ show n
        PBool n -> text $ show n
        UnaryOp n p -> text n <+> pp p
        BinaryOp n p1 p2 -> "(" <+> pp p1 <+> text n <+> pp p2 <+> ")"

instance Pretty CoreExpr where
    ppr p ex = evalState (ppr' p ex) 0
        where
            ppr' p ex = case ex of
                Lit x -> return $ text $ show x
                BLVar x -> return $ text $ show x
                BUVar x -> return $ text $ show x
                FLVar x -> return $ text $ show x
                FUVar x -> return $ text $ show x
                Abs t e -> do
                    e' <- ppr' p e
                    i <- fresh
                    return $ parensIf (p>0) $ char 'λ' <> i <+> "->" <+> pp e
                App e1 e2 -> do
                    e1' <- ppr' p e1
                    e2' <- ppr' p e2
                    return $ e1' <+> e2'
                TensorValue e1 e2 -> do
                    e1' <- ppr' p e1
                    e2' <- ppr' p e2
                    return $ parens $ e1' <> "," <+> e2'
                LetTensor e1 e2 -> do
                    e1' <- ppr' p e1
                    e2' <- ppr' p e2
                    i <- fresh
                    j <- fresh
                    return $ "let" <+> i <> "*" <> j <+> "=" <+> e1' <+> "in" <+> e2' 
                UnitValue -> return "()"
                LetUnit e1 e2 -> do
                    e1' <- ppr' p e1
                    e2' <- ppr' p e2
                    return $ "let" <+> "_" <+> "=" <+> e1' <+> "in" <+> e2' 
                WithValue e1 e2 -> do
                    e1' <- ppr' p e1
                    e2' <- ppr' p e2
                    return $ parens $ e1' <+> "|" <+> e2'
                Fst e@(App _ _) -> ("fst" <+>) . parens <$> ppr' p e
                Snd e@(App _ _) -> ("snd" <+>) . parens <$> ppr' p e
                Fst e -> ("fst" <+>) <$> ppr' p e
                Snd e -> ("snd" <+>) <$> ppr' p e
                InjL _ e -> ("inl" <+>) <$> ppr' p e
                InjR _ e -> ("inr" <+>) <$> ppr' p e
                CaseOfPlus e1 e2 e3 -> do
                    e1' <- ppr' p e1
                    e2' <- ppr' p e2
                    e3' <- ppr' p e3
                    i <- fresh
                    j <- fresh
                    return $ "case" <+> e1' <+> "of" <+> "inl" <+> i <+> "->" <+> e2' <+> "|" <+> "inr" <+> j <+> "->" <+> e3'
                BangValue e -> ("!" <>) <$> ppr' p e
                LetBang e1 e2 -> do
                    e1' <- ppr' p e1
                    e2' <- ppr' p e2
                    i <- fresh
                    return $ "let" <+> "!" <> i <+> "=" <+> e1' <+> "in" <+> e2'
                LetIn e1 e2 -> do
                    e1' <- ppr' p e1
                    e2' <- ppr' p e2
                    i <- fresh
                    return $ "let" <+> i <+> "=" <+> e1' <+> "in" <+> e2'
                e@(Mark _ _ _ (Just t) _) -> return $ "{{" <+> pp t <+> "}}"
                e@Mark {} -> return "{{ ... }}"
                CaseOf e ((tag, e1):ls) -> do
                    e' <- ppr' p e
                    e1' <- ppr' p e1
                    i <- fresh
                    ls' <- mapM (\(t', ex) -> do
                            j <- fresh
                            ex' <- ppr' p ex
                            return $ "|" <+> text t' <+> j <+> "->" <+> ex'
                        ) ls
                    return $ "case" <+> e' <+> "of" <+>
                                text tag <+> i <+> "->" <+> e1' <>
                                    foldl (<+>) P.empty ls'
                ADTVal n (Just e) -> (text n <+>) <$> ppr' p e
                ADTVal n Nothing -> return $ text n
-- showexpr' _ (CaseOf _ []) = error "Case of sum should have at least one tag"
-- showexpr' d (CaseOf e ((tag, e1):exps)) = indent d ++ "case " ++ showexpr' d e ++ " of " ++
--     indent (d+1) ++ "  " ++ tag ++ " " ++ "?" ++ " -> " ++ showexpr' (d+2) e1 ++
--         foldl (\p (t, ex) -> p ++ indent (d+1) ++ 
--             "| " ++ t ++ " " ++ "?" ++ " -> " ++
--                 showexpr' (d+2) ex) "" exps

            fresh :: State Int Doc
            fresh = get >>= \n -> put (n+1) >> return (text (getName n))



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
transformM f (Mark a n b t ed) = f $ Mark a n b t ed
transformM f (SumValue mts (s, e)) = f . SumValue mts . (,) s =<< transformM f e
transformM f (CaseOfSum e ls) = f =<< (CaseOfSum <$> transformM f e <*> traverse (\ (s, e) -> (,) s <$> transformM f e) ls)
transformM f (CaseOf e ls) = f =<< (CaseOf <$> transformM f e <*> traverse (\ (s, e) -> (,) s <$> transformM f e) ls)
transformM f (ADTVal n (Just e)) = f . ADTVal n . Just =<< transformM f e
transformM f (ADTVal n Nothing) = f $ ADTVal n Nothing


transform :: (CoreExpr -> CoreExpr) -> CoreExpr -> CoreExpr
transform f e = runIdentity (transformM (return . f) e)


transformTypeM :: (Monad m, Applicative m) => (Type -> m Type) -> Type -> m Type
transformTypeM f (TyLit x) = f $ TyLit x
transformTypeM f Unit = f Unit
transformTypeM f (Fun t1 t2) = f =<< (Fun <$> transformTypeM f t1 <*> transformTypeM f t2)
transformTypeM f (Tensor t1 t2) = f =<< (Tensor <$> transformTypeM f t1 <*> transformTypeM f t2)
transformTypeM f (With t1 t2) = f =<< (With <$> transformTypeM f t1 <*> transformTypeM f t2)
transformTypeM f (Plus t1 t2) = f =<< (Plus <$> transformTypeM f t1 <*> transformTypeM f t2)
transformTypeM f (Bang t) = f . Bang =<< transformTypeM f t
transformTypeM f (TypeVar i) = f $ TypeVar i
transformTypeM f (ExistentialTypeVar i) = f $ ExistentialTypeVar i
transformTypeM f (Sum nts) = f . Sum =<< traverse (\(n,t) -> (,) n <$> transformTypeM f t) nts
transformTypeM f (ADT n ls) = f . ADT n =<< traverse (transformTypeM f) ls
transformTypeM f (RefinementType n t ls mp) = f =<< (RefinementType n <$> transformTypeM f t <*> traverse (transformTypeM f) ls <*> pure mp)


transformType :: (Type -> Type) -> Type -> Type
transformType f e = runIdentity (transformTypeM (return . f) e)



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

isADTBool :: Type -> Bool
isADTBool t = case t of
                ADT n _ -> n == "Bool"
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

class TypeProperties a where
    isFunction :: a -> Bool

instance TypeProperties Type where
    isFunction (Fun _ _) = True
    isFunction _ = False

instance TypeProperties Scheme where
    isFunction (Forall _ (Fun _ _)) = True
    isFunction _ = False

instance (TypeProperties a, TypeProperties b) => TypeProperties (Either a b) where
    isFunction (Left x) = isFunction x
    isFunction (Right x) = isFunction x


-------------------------------------------------------------------------------
-- Util
-------------------------------------------------------------------------------

-- showexpr' d (CaseOfPlus e1 e2 e3) = indent d ++ "case " ++ showexpr' d e1 ++ " of " ++
--                                             indent (d+1) ++ "inl " ++ "?" ++ " -> " ++ showexpr' (d+2) e2 ++
--                                             indent (d+1) ++ "| inr " ++ "?" ++ " -> " ++ showexpr' (d+2) e3
-- showexpr' _ (Mark i n c t ed ) = "{{ " ++ show i ++ " : " ++ show t ++ " in context" ++ show c ++ " ?? " ++ show ed ++ " }}"
-- showexpr' d (SumValue mts (s, e)) = indent d ++ "union {" ++
--     foldl (\p (s', t) -> p ++ indent (d+2) ++ s' ++ " : " ++ show (fromJust t) ++ ";") "" mts
--     ++ indent (d+2) ++ s ++ " " ++ show e ++ ";"
--     ++ indent (d+1) ++ "}"
-- showexpr' _ (CaseOfSum _ []) = error "Case of sum should have at least one tag"
-- showexpr' d (CaseOfSum e ((tag, e1):exps)) = indent d ++ "case " ++ showexpr' d e ++ " of " ++
--     indent (d+1) ++ "  " ++ tag ++ " " ++ "?" ++ " -> " ++ showexpr' (d+2) e1 ++
--         foldl (\p (t, ex) -> p ++ indent (d+1) ++ 
--             "| " ++ t ++ " " ++ "?" ++ " -> " ++
--                 showexpr' (d+2) ex) "" exps


indent :: Int -> String
indent d = (if d == 0 then "" else "\n") ++ replicate (4*d) ' '


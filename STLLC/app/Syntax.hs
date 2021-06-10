module Syntax (Binding(..), Expr(..), Pattern(..), transformM, transform) where 

import Data.Maybe
import Prelude hiding (Bool)
import Data.Functor.Identity


import CoreSyntax (Type, Scheme, Name)



-------------------------------------------------------------------------------
-- Datatypes
-------------------------------------------------------------------------------

data Binding = Binding Name Expr


data Expr

    = Var String

    -- A -o B
    | Abs String (Maybe Type) Expr     -- \x:T -> M . with Bruijn indices
    | App Expr Expr     -- M N

    -- A (*) B
    | TensorValue Expr Expr
    | LetTensor String String Expr Expr

    -- 1
    | UnitValue
    | LetUnit Expr Expr

    -- A & B
    | WithValue Expr Expr
    | Fst Expr
    | Snd Expr

    -- A (+) B
    | InjL (Maybe Type) Expr    -- inl:B M : typeof M (+) A
    | InjR (Maybe Type) Expr    -- inr:A M : A (+) typeof M
    | CaseOfPlus Expr String Expr String Expr -- case M of inl x => N | inr y => P : C

    -- !A
    | BangValue Expr
    | LetBang String Expr Expr

    -- Non-canonical

    | LetIn String Expr Expr

    | Mark Int [(String, Scheme)] (Maybe Type)

    -- Sum types
    | SumValue [(String, Maybe Type)] (String, Expr)
    | CaseOfSum Expr [(String, String, Expr)]

    | CaseOf Expr [(String, String, Expr)]

    -- Added sugar :)

    | UnrestrictedAbs String (Maybe Type) Expr


data Pattern
    = TensorPattern String String
    | UnitPattern
    | BangPattern String
    
    | VanillaPattern String





-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance (Show Binding) where
    show (Binding s e) = "let " ++ s ++ " =\n" ++ show e ++ ";\n"


instance (Show Expr) where
    show e = showexpr' 0 e
        where
            showexpr' :: Int -> Expr -> String -- Use Int (depth) to indent the code
            showexpr' d (Var x) = x
            showexpr' d (Abs x (Just t) e) = indent d ++ "(λ" ++ x ++ " : " ++ show t ++ " -o " ++ showexpr' (d+1) e ++ ")"
            showexpr' d (Abs x Nothing e) = indent d ++ "(λ" ++ x ++ " -o " ++ showexpr' (d+1) e ++ ")"
            showexpr' d (App e1 e2) = showexpr' d e1 ++ " " ++ showexpr' d e2
            showexpr' d (TensorValue e1 e2) = "< " ++ showexpr' d e1 ++ " * " ++ showexpr' d e2 ++ " >"
            showexpr' d (LetTensor u v e1 e2) = indent d ++ "let " ++ u ++ "*" ++ v ++ " = " ++ showexpr' d e1 ++ " in " ++ showexpr' (d+1) e2
            showexpr' d UnitValue = "<>"
            showexpr' d (LetUnit e1 e2) = indent d ++ "let _ = " ++ showexpr' d e1 ++ " in " ++ showexpr' (d+1) e2
            showexpr' d (WithValue e1 e2) = "< " ++ showexpr' d e1 ++ " & " ++ showexpr' d e2 ++ " >"
            showexpr' d (Fst a@(App _ _)) = "fst (" ++ showexpr' d a ++ ")"
            showexpr' d (Snd a@(App _ _)) = "snd (" ++ showexpr' d a ++ ")"
            showexpr' d (Fst e) = "(fst " ++ showexpr' d e ++ ")"
            showexpr' d (Snd e) = "(snd " ++ showexpr' d e ++ ")"
            showexpr' d (InjL (Just t) e) = "inl " ++ showexpr' d e ++ " : " ++ show t
            showexpr' d (InjL Nothing e) = "inl " ++ showexpr' d e 
            showexpr' d (InjR (Just t) e) = "inr " ++ show t ++ " : " ++ showexpr' d e
            showexpr' d (InjR Nothing e) = "inr " ++ showexpr' d e
            showexpr' d (CaseOfPlus e1 x e2 y e3) = indent d ++ "case " ++ showexpr' d e1 ++ " of " ++
                                                        indent (d+1) ++ "  inl " ++ x ++ " => " ++ showexpr' (d+2) e2 ++
                                                        indent (d+1) ++ "| inr " ++ y ++ " => " ++ showexpr' (d+2) e3
            showexpr' d (BangValue e) = "! " ++ showexpr' d e ++ ""
            showexpr' d (LetBang x e1 e2) = indent d ++ "let !" ++ x ++ " = " ++ showexpr' d e1 ++ " in " ++ showexpr' (d+1) e2
            showexpr' d (LetIn x e1 e2) = indent d ++ "let " ++ x ++ " = " ++ showexpr' d e1 ++ " in " ++ showexpr' (d+1) e2
            showexpr' d (Mark _ _ t) = "{{ " ++ show t ++ " }}"
            showexpr' d (SumValue mts (s, e)) = indent d ++ "union {" ++
                foldl (\p (s, mt) -> p ++ indent (d+2) ++ s ++ maybe "" (\t -> " : " ++ show t) mt ++ ";") "" mts
                ++ indent (d+2) ++ s ++ " " ++ show e ++ ";"
                ++ indent (d+1) ++ "}"
            showexpr' d (CaseOfSum e ((tag, id, e1):exps)) = indent d ++ "case " ++ showexpr' d e ++ " of " ++
                                                        indent (d+1) ++ "  " ++ tag ++ " " ++ id ++ " => " ++ showexpr' (d+2) e1 ++
                                                        foldl (\p (t, i, ex) -> p ++ indent (d+1) ++ 
                                                            "| " ++ t ++ " " ++ i ++ " => " ++
                                                                showexpr' (d+2) ex) "" exps

            showexpr' d (CaseOf e ((tag, id, e1):exps)) = indent d ++ "case " ++ showexpr' d e ++ " of " ++
                                                        indent (d+1) ++ "  " ++ tag ++ " " ++ id ++ " => " ++ showexpr' (d+2) e1 ++
                                                        foldl (\p (t, i, ex) -> p ++ indent (d+1) ++ 
                                                            "| " ++ t ++ " " ++ i ++ " => " ++
                                                                showexpr' (d+2) ex) "" exps

            showexpr' d (UnrestrictedAbs x (Just t) e) = indent d ++ "(λ" ++ x ++ " : " ++ show t ++ " -> " ++ showexpr' (d+1) e ++ ")"
            showexpr' d (UnrestrictedAbs x Nothing e) = indent d ++ "(λ" ++ x ++ " -> " ++ showexpr' (d+1) e ++ ")"

            indent d = (if d == 0 then "" else "\n") ++ replicate (4*d) ' '





-------------------------------------------------------------------------------
-- Traversal
-------------------------------------------------------------------------------

transformM :: (Monad m, Applicative m) => (Expr -> Expr) -> Expr -> m Expr
transformM f (Var x) = pure $ f $ Var x
transformM f (Abs x t e) = f <$> (Abs x t <$> transformM f e)
transformM f (App e1 e2) = f <$> (App <$> transformM f e1 <*> transformM f e2)
transformM f (TensorValue e1 e2) = f <$> (TensorValue <$> transformM f e1 <*> transformM f e2)
transformM f (LetTensor x y e1 e2) = f <$> (LetTensor x y <$> transformM f e1 <*> transformM f e2)
transformM f UnitValue = pure $ f UnitValue
transformM f (LetUnit e1 e2) = f <$> (LetUnit <$> transformM f e1 <*> transformM f e2)
transformM f (WithValue e1 e2) = f <$> (WithValue <$> transformM f e1 <*> transformM f e2)
transformM f (Fst e) = f <$> (Fst <$> transformM f e)
transformM f (Snd e) = f <$> (Snd <$> transformM f e)
transformM f (InjL t e) = f <$> (InjL t <$> transformM f e)
transformM f (InjR t e) = f <$> (InjR t <$> transformM f e)
transformM f (CaseOfPlus e1 x e2 y e3) = f <$> (CaseOfPlus <$> transformM f e1 <*> pure x <*> transformM f e2 <*> pure y <*> transformM f e3)
transformM f (BangValue e) = f <$> (BangValue <$> transformM f e)
transformM f (LetBang x e1 e2) = f <$> (LetBang x <$> transformM f e1 <*> transformM f e2)
transformM f (LetIn x e1 e2) = f <$> (LetIn x <$> transformM f e1 <*> transformM f e2)
transformM f (Mark a b t) = pure $ f $ Mark a b t
transformM f (SumValue mts (s, e)) = f <$> (SumValue mts . (,) s <$> transformM f e)
transformM f (CaseOfSum e ls) = f <$> (CaseOfSum <$> transformM f e <*> traverse (\ (s, s', e) -> (,,) s s' <$> transformM f e) ls)
transformM f (CaseOf e ls) = f <$> (CaseOf <$> transformM f e <*> traverse (\ (s, s', e) -> (,,) s s' <$> transformM f e) ls)


transform :: (Expr -> Expr) -> Expr -> Expr
transform f e = runIdentity (transformM f e)


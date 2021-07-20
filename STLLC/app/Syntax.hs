{-# LANGUAGE LambdaCase, DeriveGeneric, DeriveAnyClass #-}
module Syntax (Binding(..), Expr(..), Pattern(..), transformM, transform, isInExpr) where 

import Data.Maybe
import Control.Monad.State
import GHC.Generics (Generic)
import Control.DeepSeq
import Data.Functor.Identity


import CoreSyntax (Type, Scheme, Name, Literal(..))



-------------------------------------------------------------------------------
-- Datatypes
-------------------------------------------------------------------------------

data Binding = Binding Name Expr
    deriving (Generic, NFData)


data Expr

    = Lit Literal
    | Var Name

    -- A -o B
    | Abs Name (Maybe Type) Expr     -- \x:T -> M . with Bruijn indices
    | App Expr Expr     -- M N

    -- A (*) B
    | TensorValue Expr Expr
    | LetTensor Name Name Expr Expr

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
    | CaseOfPlus Expr Name Expr Name Expr -- case M of inl x => N | inr y => P : C

    -- !A
    | BangValue Expr
    | LetBang Name Expr Expr

    -- Non-canonical

    | LetIn Name Expr Expr

    | Mark Int (Maybe Name) ([(Name, Either Scheme Type)], [(Name, Type)]) (Maybe Scheme) (Int, [Name], Int)

    -- Sum types
    | SumValue [(Name, Maybe Type)] (Name, Expr)
    | CaseOfSum Expr [(Name, Name, Expr)]

    | CaseOf Expr [(Name, Name, Expr)]

    -- Added sugar :)

    | UnrestrictedAbs Name (Maybe Type) Expr
    deriving (Generic, NFData, Eq)


data Pattern
    = TensorPattern String String
    | UnitPattern
    | BangPattern String
    
    | VanillaPattern String





-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance (Show Binding) where
    show (Binding s e) =
            s ++ concatMap (' ':) (viewVars e) ++ " = " ++ show (viewBody e) ++ ";\n"
        where
            viewVars (Abs n _ e') = n : viewVars e'
            viewVars _ = []

            viewBody (Abs n _ e) = viewBody e
            viewBody e = e


instance (Show Expr) where
    show e = showexpr' 0 e
        where
            showexpr' :: Int -> Expr -> String -- Use Int (depth) to indent the code
            showexpr' d (Lit x) = show x
            showexpr' d (Var x) = x
            -- showexpr' d (Abs x (Just t) e) = indent d ++ "(λ" ++ x ++ " : " ++ show t ++ " -o " ++ showexpr' (d+1) e ++ ")"
            showexpr' d (Abs x _ e) = "(λ" ++ x ++ " -> " ++ showexpr' (d+1) e ++ ")"
            showexpr' d (App e1 e2@(App _ _)) = showexpr' d e1 ++ " (" ++ showexpr' d e2 ++ ")"
            showexpr' d (App e1 e2) = showexpr' d e1 ++ " " ++ showexpr' d e2
            showexpr' d (TensorValue e1 e2) = "(" ++ showexpr' d e1 ++ ", " ++ showexpr' d e2 ++ ")"
            showexpr' d (LetTensor u v e1 e2) = indent d ++ "let " ++ u ++ "*" ++ v ++ " = " ++ showexpr' d e1 ++ " in " ++ showexpr' (d+1) e2
            showexpr' d UnitValue = "()"
            showexpr' d (LetUnit e1 e2) = indent d ++ "let _ = " ++ showexpr' d e1 ++ " in " ++ showexpr' (d+1) e2
            showexpr' d (WithValue e1 e2) = "( " ++ showexpr' d e1 ++ " | " ++ showexpr' d e2 ++ " )"
            showexpr' d (Fst a@(App _ _)) = "(fst (" ++ showexpr' d a ++ "))"
            showexpr' d (Snd a@(App _ _)) = "(snd (" ++ showexpr' d a ++ "))"
            showexpr' d (Fst e) = "(fst " ++ showexpr' d e ++ ")"
            showexpr' d (Snd e) = "(snd " ++ showexpr' d e ++ ")"
            -- showexpr' d (InjL (Just t) e) = "inl " ++ showexpr' d e ++ " : " ++ show t
            showexpr' d (InjL _ e@(App _ _)) = "inl (" ++ showexpr' d e ++ ")"
            showexpr' d (InjL _ e) = "inl " ++ showexpr' d e
            -- showexpr' d (InjR (Just t) e) = "inr " ++ show t ++ " : " ++ showexpr' d e
            showexpr' d (InjR _ e@(App _ _)) = "inr (" ++ showexpr' d e ++ ")"
            showexpr' d (InjR _ e) = "inr " ++ showexpr' d e
            showexpr' d (CaseOfPlus e1 x e2 y e3) = indent d ++ "case " ++ showexpr' d e1 ++ " of " ++
                                                        indent (d+1) ++ "  inl " ++ x ++ " -> " ++ showexpr' (d+2) e2 ++
                                                        indent (d+1) ++ "| inr " ++ y ++ " -> " ++ showexpr' (d+2) e3
            showexpr' d (BangValue e) = "(!" ++ showexpr' d e ++ ")"
            showexpr' d (LetBang x e1 e2) = indent d ++ "let !" ++ x ++ " = " ++ showexpr' d e1 ++ " in " ++ showexpr' (d+1) e2
            showexpr' d (LetIn x e1 e2) = indent d ++ "let " ++ x ++ " = " ++ showexpr' d e1 ++ " in " ++ showexpr' (d+1) e2
            showexpr' d (Mark _ _ _ (Just t) _) = "{{ " ++ show t ++ " }}"
            showexpr' d Mark {} = "{{ ... }}"
            showexpr' d (SumValue mts (s, e)) = indent d ++ "union {" ++
                foldl (\p (s, mt) -> p ++ indent (d+2) ++ s ++ maybe "" (\t -> " : " ++ show t) mt ++ ";") "" mts
                ++ indent (d+2) ++ s ++ " " ++ show e ++ ";"
                ++ indent (d+1) ++ "}"
            showexpr' d (CaseOfSum e ((tag, id, e1):exps)) = indent d ++ "case " ++ showexpr' d e ++ " of " ++
                                                        indent (d+1) ++ "  " ++ tag ++ " " ++ id ++ " -> " ++ showexpr' (d+2) e1 ++
                                                        foldl (\p (t, i, ex) -> p ++ indent (d+1) ++ 
                                                            "| " ++ t ++ " " ++ i ++ " -> " ++
                                                                showexpr' (d+2) ex) "" exps

            showexpr' d (CaseOf e ((tag, id, e1):exps)) = indent d ++ "case " ++ showexpr' d e ++ " of " ++
                                                        indent (d+1) ++ "  " ++ tag ++ " " ++ id ++ " -> " ++ showexpr' (d+2) e1 ++
                                                        foldl (\p (t, i, ex) -> p ++ indent (d+1) ++ 
                                                            "| " ++ t ++ " " ++ i ++ " -> " ++
                                                                showexpr' (d+2) ex) "" exps

            -- showexpr' d (UnrestrictedAbs x (Just t) e) = indent d ++ "(λ" ++ x ++ " : " ++ show t ++ " -> " ++ showexpr' (d+1) e ++ ")"
            showexpr' d (UnrestrictedAbs x _ e) = indent d ++ "(λ" ++ x ++ " => " ++ showexpr' (d+1) e ++ ")"

            indent d = (if d == 0 then "" else "\n") ++ replicate (4*d) ' '





-------------------------------------------------------------------------------
-- Traversal
-------------------------------------------------------------------------------

transformM :: (Monad m, Applicative m) => (Expr -> m Expr) -> Expr -> m Expr
transformM f (Lit x) = f $ Lit x
transformM f (Var x) = f $ Var x
transformM f (Abs x t e) = f . Abs x t =<< transformM f e
transformM f (App e1 e2) = f =<< (App <$> transformM f e1 <*> transformM f e2)
transformM f (TensorValue e1 e2) = f =<< (TensorValue <$> transformM f e1 <*> transformM f e2)
transformM f (LetTensor x y e1 e2) = f =<< (LetTensor x y <$> transformM f e1 <*> transformM f e2)
transformM f UnitValue = f UnitValue
transformM f (LetUnit e1 e2) = f =<< (LetUnit <$> transformM f e1 <*> transformM f e2)
transformM f (WithValue e1 e2) = f =<< (WithValue <$> transformM f e1 <*> transformM f e2)
transformM f (Fst e) = f . Fst =<< transformM f e
transformM f (Snd e) = f . Snd =<< transformM f e
transformM f (InjL t e) = f . InjL t =<< transformM f e
transformM f (InjR t e) = f . InjR t =<< transformM f e
transformM f (CaseOfPlus e1 x e2 y e3) = f =<< (CaseOfPlus <$> transformM f e1 <*> pure x <*> transformM f e2 <*> pure y <*> transformM f e3)
transformM f (BangValue e) = f . BangValue =<< transformM f e
transformM f (LetBang x e1 e2) = f =<< (LetBang x <$> transformM f e1 <*> transformM f e2)
transformM f (LetIn x e1 e2) = f =<< (LetIn x <$> transformM f e1 <*> transformM f e2)
transformM f (Mark a b c t ed) = f $ Mark a b c t ed
transformM f (SumValue mts (s, e)) = f . SumValue mts . (,) s =<< transformM f e
transformM f (CaseOfSum e ls) = f =<< (CaseOfSum <$> transformM f e <*> traverse (\ (s, s', e) -> (,,) s s' <$> transformM f e) ls)
transformM f (CaseOf e ls) = f =<< (CaseOf <$> transformM f e <*> traverse (\ (s, s', e) -> (,,) s s' <$> transformM f e) ls)
transformM f (UnrestrictedAbs x t e) = f . UnrestrictedAbs x t =<< transformM f e


transform :: (Expr -> Expr) -> Expr -> Expr
transform f e = runIdentity (transformM (return . f) e)


isInExpr :: Expr -> Expr -> Bool
isInExpr e1 e2 = execState (transformM (\e' -> do
                    when (e1 == e') (put True)
                    return e'
               ) e2) False

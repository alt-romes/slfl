{-# LANGUAGE LambdaCase, DeriveGeneric, DeriveAnyClass, OverloadedStrings #-}
module Syntax (Binding(..), Expr(..), Pattern(..), transformM, transform, isInExpr) where 

import Data.Maybe
import Control.Monad.State
import GHC.Generics (Generic)
import Control.DeepSeq
import Prelude hiding ((<>))
import Text.PrettyPrint
import Data.Functor.Identity


import CoreSyntax (Type, Scheme, Name, Literal(..))
import Util



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
    = TensorPattern Name Name
    | UnitPattern
    | BangPattern Name
    
    | VanillaPattern Name





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
    show = render . ppr 0

    -- indent d = (if d == 0 then "" else "\n") ++ replicate (4*d) ' '


instance Pretty Expr where
    ppr p e = case e of
        Syntax.Lit l -> ppr p l
        Syntax.Var x -> text x
        Syntax.Abs x Nothing e -> parensIf (p>0) $ char 'λ' <> text x <+> text "->" <+> ppr (p+1) e
        Syntax.Abs x (Just t) e -> parensIf (p>0) $ char 'λ' <> text x <+> char ':' <+> pp t <+> text "->" <+> ppr (p+1) e
        Syntax.App e1 e2@(App _ _) -> ppr (p+1) e1 <+> parens (ppr (p+1) e2)
        Syntax.App e1 e2 -> ppr (p+1) e1 <+> ppr (p+1) e2
        Syntax.TensorValue e1 e2 -> char '(' <> ppr p e1 <> char ',' <+> ppr p e2 <> char ')'
        Syntax.LetTensor u v e1 e2 -> text "let" <+> text u <> char '*' <> text v <+> char '=' <+> ppr p e1 <+> text "in" <+> ppr p e2
        Syntax.UnitValue -> text "()"
        Syntax.LetUnit e1 e2 -> text "let" <+> char '_' <+> char '=' <+> ppr p e1 <+> text "in" <+> ppr p e2
        Syntax.WithValue e1 e2 -> char '(' <> ppr p e1 <+> char '|' <+> ppr p e2 <> char ')'
        Syntax.Fst e@(App _ _) -> text "fst" <+> parens (ppr (p+1) e)
        Syntax.Snd e@(App _ _) -> text "snd" <+> parens (ppr (p+1) e)
        Syntax.Fst e -> text "fst" <+> ppr (p+1) e
        Syntax.Snd e -> text "snd" <+> ppr (p+1) e
        Syntax.InjL Nothing e -> text "inl" <+> ppr (p+1) e
        Syntax.InjL (Just t) e -> text "inl" <+> ppr (p+1) e <+> char ':' <+> pp t
        Syntax.InjR Nothing e -> text "inr" <+> ppr (p+1) e
        Syntax.InjR (Just t) e -> text "inr" <+> pp t <+> char ':' <+> ppr (p+1) e
        Syntax.CaseOfPlus e1 x e2 y e3 -> text "case" <+> ppr p e1 <+> text "of" <+> text "inl" <+> text x <+> text "->" <+> ppr p e2 <+> char '|' <+> text "inr" <+> text y <+> text "->" <+> ppr p e3
        Syntax.BangValue e -> parens $ char '!' <> ppr p e
        Syntax.LetBang x e1 e2 -> text "let" <+> char '!' <> text x <+> char '=' <+> ppr p e1 <+> text "in" <+> ppr p e2
        Syntax.LetIn x e1 e2 -> text "let" <+> text x <+> char '=' <+> ppr p e1 <+> text "in" <+> ppr p e2
        Syntax.Mark _ _ _ (Just t) _ -> text "{{" <+> pp t <+> text "}}"
        Syntax.Mark {} -> text "{{" <+> text "..." <+> text "}}"
        Syntax.SumValue mts (s, e) -> text "union" <+> char '{' <+> foldl undefined empty mts <+> text s <+> pp e <+> char '}' -- TODO
        Syntax.CaseOfSum e ((tag, id, e1):exps) -> undefined -- TODO
        Syntax.CaseOf e ((tag, id, e1):exps) -> "case" <+> pp e <+> "of" <+>
                                                    text tag <+> text id <+> "->" <+> pp e1 <+>
                                                        foldl (\p (t, i, ex) -> p <+> "|" <+> text t <+> text i <+> "->" <+> pp ex) empty exps
        UnrestrictedAbs x Nothing e -> parensIf (p>0) $ char 'λ' <> text x <+> text "=>" <+> ppr (p+1) e
        UnrestrictedAbs x (Just t) e -> parensIf (p>0) $ char 'λ' <> text x <+> char ':' <+> pp t <+> text "=>" <+> ppr (p+1) e

        -- showexpr' d (SumValue mts (s, e)) = indent d ++ "union {" ++
        --     foldl (\p (s, mt) -> p ++ indent (d+2) ++ s ++ maybe "" (\t -> " : " ++ show t) mt ++ ";") "" mts
        --     ++ indent (d+2) ++ s ++ " " ++ show e ++ ";"
        --     ++ indent (d+1) ++ "}"
        -- showexpr' d (CaseOfSum e ((tag, id, e1):exps)) = indent d ++ "case " ++ showexpr' d e ++ " of " ++
        --                                             indent (d+1) ++ "  " ++ tag ++ " " ++ id ++ " -> " ++ showexpr' (d+2) e1 ++
        --                                             foldl (\p (t, i, ex) -> p ++ indent (d+1) ++ 
        --                                                 "| " ++ t ++ " " ++ i ++ " -> " ++
        --                                                     showexpr' (d+2) ex) "" exps

        -- showexpr' d (CaseOf e ((tag, id, e1):exps)) = indent d ++ "case " ++ showexpr' d e ++ " of " ++
        --                                             indent (d+1) ++ "  " ++ tag ++ " " ++ id ++ " -> " ++ showexpr' (d+2) e1 ++
        --                                             foldl (\p (t, i, ex) -> p ++ indent (d+1) ++ 
        --                                                 "| " ++ t ++ " " ++ i ++ " -> " ++
        --                                                     showexpr' (d+2) ex) "" exps





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

{-# LANGUAGE LambdaCase #-}
module Minimize where

import CoreSyntax (Name)
import Syntax
import Program



minimize :: Program -> Program
minimize (Program a binds c d) = Program a (map minimize' binds) c d
    where
        minimize' :: Binding -> Binding
        minimize' (Binding n e) = Binding n $ minimizex e


minimizex :: Expr -> Expr
minimizex = transform $ \case
    a@Abs {} -> simplifyAbs a [] a
    x -> x


-- Simplify `(\x -> \y -> name x y)` to `name`
simplifyAbs :: Expr -> [Name] -> Expr -> Expr
simplifyAbs orig ls (Abs x t e) = simplifyAbs orig (x:ls) e -- Enter lambda
simplifyAbs o [x] (App e1 e2) =     -- Found an application and there's only one name in the "context"
    case e2 of
      Var n -> if n == x then e1    -- If e2 is the var name equal to the last name, return e1 as the minimized exp
                         else o     -- Else we fail and return the original expression
      _ -> o
simplifyAbs o (x:xs) (App e1 e2) =
    case e2 of
      Var n -> if n == x then simplifyAbs o xs e1 -- Same as above but deepen
                         else o
      _ -> o


-- The minimization reached a type that doesn't work, return the original expression
simplifyAbs o [] (App e1 e2) = o
simplifyAbs o _ _ = o 


module Expression where 

import Prelude hiding (Bool,True,False)


-- E ::= Zero | Succ E | True | False | isZero E | If E1 then E2 else E3
-- T ::= Nat | Bool

data Expr 
    = Zero 
    | Succ Expr 
    | True 
    | False
    | IsZero Expr 
    | If Expr Expr Expr 
    deriving (Eq,Show)



data Type 
    = Nat 
    | Bool
    deriving (Eq,Show)
 

typeOf :: Expr -> Maybe Type
typeOf Zero = return Nat
typeOf (Succ e) = do 
    t <- typeOf e
    return t 
typeOf True = return Bool 
typeOf False = return Bool 
typeOf (IsZero e) = do
    t <- typeOf e
    case t of 
        Nat -> return Bool
        _ -> Nothing
typeOf (If e1 e2 e3) = do 
    t1 <- typeOf e1
    case t1 of 
        Bool -> do
            t2 <- typeOf e2 
            t3 <- typeOf e3
            if (t2==t3) then return t2 
                        else Nothing 
        _ -> Nothing
   
   

{-
-- Zero : Nat
typeOf Zero = Just Nat 

 --  e : Nat
 -- Succ e : Nat
typeOf (Succ e) = 
    case (typeOf e) of 
        Just Nat -> Just Nat
        _ -> Nothing 
        
typeOf True = Just Bool 
typeOf False = Just Bool 
typeOf (IsZero e) = 
        case (typeOf e) of 
        Just Nat -> Just Bool 
        _ -> Nothing 
typeOf (If e1 e2 e3) = 
        case (typeOf e1) of
        Just Bool -> 
            let t2 = typeOf e2 
                t3 = typeOf e3 in 
                    if (t2==t3) then t2 else Nothing
        _ -> Nothing 
-}




module Check where 

import Data.Maybe
import Prelude hiding (True,False,Bool)

import Syntax 

type Env = [(Id,Type)]


typeOf :: Env -> Expr -> Maybe Type

-- Base values
typeOf _ True = return Bool 

typeOf _ False = return Bool 

typeOf _ UnitV = return Unit

typeOf ctxt (Zero) = return Nat


--   (x:T) in Gamma
--   Gamma |- x : T
typeOf ctxt (Var x) = do
     t <- lookup x ctxt
     return t

-- Gamma |- t1 : Nat
-- Gamma |- Succ t1 : Nat
typeOf ctxt (Succ e1) = do
    t1 <- typeOf ctxt e1
    case t1 of
        Nat -> return Nat
        _ -> Nothing
 

-- Gamma |- E1 : T -> S   Gamma |- E2 : T
-- Gamma |- E1 E2 : S
typeOf ctxt (App e1 e2) = do
    t1 <- typeOf ctxt e1 
    case t1 of 
        Fun t s -> do 
            t2 <- typeOf ctxt e2 
            if (t2 == t) then return s 
                         else Nothing 
        _ -> Nothing


-- lambda x:T1 . lambda x:T2 . x :: T1 -> T2 -> T2
-- Gamma , x:T |- E : S 
-- Gamma |- lambda x:T . E : T -> S
typeOf ctxt (Abs x t e) = do
    s <- typeOf ((x,t):ctxt) e
    return $ Fun t s


-- Gamma |- e1 : Bool   Gamma |- e2 : T     Gamma |- e3 : T
-- Gamma |- if e1 e2 e3 : T
typeOf ctxt (If e1 e2 e3) = do
    t1 <- typeOf ctxt e1
    case t1 of 
        Bool -> do
            t2 <- typeOf ctxt e2 
            t3 <- typeOf ctxt e3
            if (t2==t3) then return t2 
                        else Nothing 
        _ -> Nothing


-- Simple Extensions

-- Unit
-- Gamma |- t1 : Unit   Gamma |- t2 : T
-- Gamma |- t1;t2 : T
typeOf ctxt (Seqnc e1 e2) = do
    t1 <- typeOf ctxt e1
    case t1 of
        Unit -> typeOf ctxt e2
        _ -> Nothing


-- Ascription; t1 as T
-- Gamma |- t1 : T
-- Gamma |- t1 as T : T
typeOf ctxt (Ascript e1 t2) = do
    t1 <- typeOf ctxt e1
    if (t1 == t2) then return t2
    else Nothing


-- Let; let x=t1 in t2
-- Gamma |- t1 : T1     Gamma, t1 : T1 |- t2 : T2
-- Gamma |- let x=t1 in t2 : T2
typeOf ctxt (LetIn x e1 e2) = do
    t1 <- typeOf ctxt e1
    typeOf ((x,t1):ctxt) e2


-- Pair; {t1, t2}
-- Gamma |- t1 : T1     Gamma |- t2 : T2
-- Gamma |- {t1, t2} : T1xT2
typeOf ctxt (PairV e1 e2) = do
    t1 <- typeOf ctxt e1
    t2 <- typeOf ctxt e2
    return (Pair t1 t2)
    

-- First; t.1
-- Gamma |- t1 : T1 x T2
-- Gamma |- t1.1 : T1
typeOf ctxt (First e1) = do
    p <- typeOf ctxt e1
    case p of
        (Pair t2 t3) -> return t2
        _ -> Nothing


-- Second; t.2
-- Gamma |- t1 : T1 x T2
-- Gamma |- t1.2 : T2
typeOf ctxt (Second e1) = do
    p <- typeOf ctxt e1
    case p of
        (Pair t2 t3) -> return t3
        _ -> Nothing


-- Tuple; {t1,t2,t3,...}
-- for each i, Gamma |- ti : Ti
-- Gamma |- {ti...} : {Ti...}
typeOf ctxt (TupleV l) =
    let typelist = catMaybes $ map (\x -> typeOf ctxt x) l in
    if ((length typelist) == (length l)) then
        return $ Tuple typelist
    else
        Nothing


-- Project; t.i
-- Gamma |- t1 : {Ti...}
-- Gamma |- t1.j : Tj
typeOf ctxt (Project i e1) = do
    t1 <- typeOf ctxt e1
    case t1 of
        (Tuple l) -> return (l !! i)
        _ -> Nothing



check :: Expr -> Maybe Type
check = typeOf []

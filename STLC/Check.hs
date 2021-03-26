
module Check where 

import Data.Maybe
import Prelude hiding (True,False,Bool)

import Syntax 

type Env = [(Id,Type)]


typeOf :: Env -> Expr -> Maybe Type

--   (x:T) in Gamma
--   Gamma |- x : T
typeOf ctxt (Var x) = do
     t <- lookup x ctxt
     return t
 
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

typeOf _ True = return Bool 
typeOf _ False = return Bool 

typeOf ctxt (If e1 e2 e3) = do
    t1 <- typeOf ctxt e1
    case t1 of 
        Bool -> do
            t2 <- typeOf ctxt e2 
            t3 <- typeOf ctxt e3
            if (t2==t3) then return t2 
                        else Nothing 
        _ -> Nothing
   

check :: Expr -> Maybe Type
check = typeOf []


module TypeCheck where

import CoreSyntax

type Ctxt = [(String,Type)]

-- Delta |- M : A 
-- DeltaI / DeltaO |- M : A
 
check :: Ctxt -> CoreExpr -> Maybe (Type , Ctxt)

-- Delta1 |- e1 : A     Delta2 |- e2 : B
------------------------------------------
-- Delta1,Delta2 |- MPair e1 e2 : A*B

-- DeltaI/DeltaO1 |- e1 : A     DeltaO1 / DeltaO2 |- e2 : B
--------------------------------------------------------------
-- DeltaI/DeltaO2 |- MPair e1 e2 : A*B

check ctx (TensorValue e1 e2) = do 
    (t1,ctx1) <- check ctx e1
    (t2,ctx2) <- check ctx1 e2
    return (t1 `Tensor` t2 , ctx2 )



-- Delta , x:A |- M : B
--------------------------------------------
-- Delta |- Abs x A M : A -o B

-- DeltaI,x:A / DeltaO |- M : B     (x not in DeltaO)
--------------------------------------------
-- DeltaI / DeltaO | - Abs x A M : A -o B

-- check ctx (Abs x t1 e) = do 
--     (t2,ctx1) <- check ((x,t1):ctx) e
--     let m = lookup x ctx1 
--     case m of
--         Nothing -> Just (Fun t1 t2 , ctx1)
--         _ -> Nothing





-------------------------
-- . |- MUnit : Unit

-----------------------------------
-- DeltaI / DeltaI |- MUnit : Unit

check ctx UnitValue =  
    return (Unit,ctx)


-- x:A |- LVar x : A

-- DeltaI,x:A / DeltaI |- LVar x : A 


-- check ctx (BLVar x) = do
--     let (mt,ctx') = findDelete x ctx []
--     t <- mt
--     return (t , ctx')





    where 
    findDelete _ [] _ = (Nothing, [])
    findDelete x ((y,t):xs) acc = if x==y then (Just t, reverse acc ++ xs) else 
                                findDelete x xs ((y,t):acc)



-- Delta1 |- e1 : A-oB       Delta2 |- e2 : A
---------------------------------------------------
-- Delta1 , Delta2 |- App e1 e2 : B


-- DeltaI / DeltaO1 |- e1 : A-oB      DeltaO1 / DeltaO2 |- e2 : A
----------------------------------------------------------------------
-- DeltaI / DeltaO2  |- App e1 e2 : B



check ctx (App e1 e2) = do 
    (Fun t1 t2,ctx1) <- check ctx e1 
    (t,ctx2) <- check ctx1 e2
    if t1==t then 
        Just (t2,ctx2)
    else 
        Nothing



-- Delta1 |- e1 : A*B     Delta2, x:A, y:B |- e2 : C    
--------------------------------------------------------
-- Delta1,Delta2 |- LetTens x e1 e2 : C


-- DeltaI / DeltaO |- e1 : A*B   DeltaO,x:A,y:B /DeltaO2  |- e2: C    x e y not in DeltaO2
-- DeltaI / DeltaO2 |- ... : C
check ctx (LetTensor x y e1 e2) = do
    (Tensor t1 t2 , ctx1) <- check ctx e1 
    ( t , ctx2) <- check ((x,t1):(y,t2):ctx1) e2
    let m1 = lookup x ctx2 
    let m2 = lookup y ctx2
    case (m1,m2) of
        (Nothing , Nothing ) -> Just (t ,ctx2)
        _ -> Nothing 



-- Delta1 |- M : 1      Delta2 |- N : C
-- Delta1,Delta2 |- let 1 = M in N : C
check ctx (LetUnit e1 e2) = do
    (Unit, ctx1) <- check ctx e1 
    check ctx1 e2 





---                                       .....
-- x:1/x:1 |- <> : 1             x:1 / empty   |-  let 1 = x in <> : 1
---------------------------------------------------------------------- *I
-- x:1/empty   |- <> * (let 1 = x in <>) : 1 * 1     x not in empty :)
--------------------------------------------------------------- -oI
-- empty/ empty |- \x:1 . <> * (let 1 = x in <>) : 1 -o 1 * 1




check ctxt Tru = return (Bool, ctxt)
check ctxt Fls = return (Bool, ctxt)



-- top level

typecheck :: CoreExpr -> Type
typecheck e = maybe (error "typecheck") fst (check [] e)

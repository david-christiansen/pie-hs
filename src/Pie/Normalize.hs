module Pie.Normalize where

import Pie.Fresh
import Pie.Panic
import Pie.Types

newtype Norm a =
  Norm
    { runNormalize :: [Symbol] -> Env Value -> a }

instance Functor Norm where
  fmap f (Norm action) = Norm (\ bound env -> f (action bound env))

instance Applicative Norm where
  pure x = Norm (\ bound env -> x)
  Norm fun <*> Norm arg = Norm (\bound env -> fun bound env (arg bound env))

instance Monad Norm where
  return = pure
  Norm val >>= f =
    Norm (\bound env -> runNormalize (f (val bound env)) bound env)

getEnv :: Norm (Env Value)
getEnv = Norm (\ bound env -> env)

getBound :: Norm [Symbol]
getBound = Norm (\ bound env -> bound)

withEnv :: Env Value -> Norm a -> Norm a
withEnv env (Norm act) =
  Norm (\bound _ -> act bound env)

inBound :: Symbol -> Norm a -> Norm a
inBound x (Norm act) =
  Norm (\bound env -> act (x:bound) env)

fresh :: Symbol -> Norm Symbol
fresh x =
  do bound <- getBound
     return (freshen bound x)

close :: Core -> Norm (Closure Value)
close expr =
  do env <- getEnv
     return (Closure env expr)

extend :: Env a -> Symbol -> a -> Env a
extend env x v = env :> (x, v)

instantiate :: Closure Value -> Symbol -> Value -> Norm Value
instantiate (Closure env expr) x v =
  withEnv (extend env x v) $
    eval expr


var :: Symbol -> Norm Value
var x = getEnv >>= var'
  where
    var' None =
      panic ("Variable not found in environment: " ++ show x)
    var' (env :> (y, v))
      | x == y    = return v
      | otherwise = var' env

eval :: Core -> Norm Value
eval (CTick x) = return (VTick x)
eval CAtom     = return VAtom
eval CZero     = return VZero
eval (CAdd1 n) = VAdd1 <$> eval n
eval (CIndNat tgt mot base step) =
  do tgtv <- eval tgt
     motv <- eval mot
     basev <- eval base
     stepv <- eval step
     doIndNat tgtv motv basev stepv
eval CNat      = return VNat
eval (CVar x)  = var x
eval (CPi x dom ran) =
  VPi x <$> eval dom <*> close ran
eval (CLambda x body) =
  VLambda x <$> close body
eval (CApp rator rand) =
  do fun <- eval rator
     arg <- eval rand
     doApply fun arg
eval (CSigma x a d) =
  VSigma x <$> eval a <*> close d
eval (CCons a d) = VCons <$> eval a <*> eval d
eval (CCar p) = eval p >>= doCar
eval (CCdr p) = eval p >>= doCdr
eval CTrivial = return VTrivial
eval CSole = return VSole
eval (CEq ty from to) = VEq <$> eval ty <*> eval from <*> eval to
eval (CSame e) = VSame <$> eval e
eval (CReplace tgt mot base) =
  do tgtv <- eval tgt
     motv <- eval mot
     basev <- eval base
     doReplace tgtv motv basev
eval (CTrans tgt1 tgt2) =
  do v1 <- eval tgt1
     v2 <- eval tgt2
     doTrans v1 v2
eval (CCong e1 e2 e3) =
  do v1 <- eval e1
     v2 <- eval e2
     v3 <- eval e3
     doCong v1 v2 v3
eval (CSymm p) = eval p >>= doSymm
eval (CIndEq tgt mot base) =
  do tgtv <- eval tgt
     motv <- eval mot
     basev <- eval base
     doIndEq tgtv motv basev
eval (CVec elem len) = VVec <$> eval elem <*> eval len
eval CVecNil = return VVecNil
eval (CVecCons e es) = VVecCons <$> eval e <*> eval es
eval (CVecHead es) = eval es >>= doHead
eval (CVecTail es) = eval es >>= doTail
eval (CIndVec k es mot base step) =
  do kv <- eval k
     esv <- eval es
     motv <- eval mot
     basev <- eval base
     stepv <- eval step
     doIndVec kv esv motv basev stepv
eval CU = return VU
eval (CThe _ e) = eval e


doApply :: Value -> Value -> Norm Value
doApply (VLambda x clos) arg =
  instantiate clos x arg
doApply (VNeu (VPi x a b) f) arg =
  VNeu <$> (instantiate b x arg)
       <*> pure (NApp f (NThe a arg))
doApply other arg = panic ("Not a function: " ++ show other)

doCar (VCons a _) = pure a
doCar (VNeu (VSigma x aT dT) ne) = pure (VNeu aT (NCar ne))

doCdr (VCons _ d) = pure d
doCdr p@(VNeu (VSigma x aT dT) ne) =
  do a <- doCar p
     t <- instantiate dT x a
     return (VNeu t (NCdr ne))

doIndNat VZero          mot base step = return base
doIndNat (VAdd1 k)      mot base step =
  do soFar <- doIndNat k mot base step
     thisStep <- doApply step k
     doApply thisStep soFar
doIndNat tgt@(VNeu VNat ne) mot base step =
  do t <- doApply mot tgt
     k <- fresh (sym "k")
     let motTy = VPi k VNat (Closure None CU)
     baseTy <- doApply mot VZero
     soFar <- fresh (sym "so-far")
     motName <- fresh (sym "mot")
     stepTy <- withEnv (None :> (motName, mot)) $
               eval (CPi k CNat
                      (CPi soFar (CApp (CVar motName) (CVar k))
                        (CApp (CVar motName) (CAdd1 (CVar k)))))
     return (VNeu t (NIndNat ne (NThe motTy mot) (NThe baseTy base) (NThe stepTy step)))

doReplace :: Value -> Value -> Value -> Norm Value
doReplace (VSame v) mot base = return base
doReplace (VNeu (VEq ty from to) ne) mot base =
  do ty <- doApply mot to
     x <- fresh (sym "x")
     baseT <- doApply mot from
     return (VNeu ty (NReplace ne
                       (NThe (VPi x ty (Closure None CU)) mot)
                       (NThe baseT base)))

doTrans :: Value -> Value -> Norm Value
doTrans (VSame v) (VSame _) = return (VSame v)
doTrans (VSame from) (VNeu (VEq t _ to) ne) =
  return (VNeu (VEq t from to) (NTrans2 (NThe (VEq t from from) (VSame from)) ne))
doTrans (VNeu (VEq t from _) ne) (VSame to) =
  return (VNeu (VEq t from to) (NTrans1 ne (NThe (VEq t to to) (VSame to))))
doTrans (VNeu (VEq t from _) ne1) (VNeu (VEq _ _ to) ne2) =
  return (VNeu (VEq t from to) (NTrans12 ne1 ne2))

doCong (VSame v) _ fun =
  VSame <$> doApply fun v
doCong (VNeu (VEq t from to) ne) ret fun =
  do from' <- doApply fun from
     to' <- doApply fun to
     x <- fresh (sym "x")
     a <- fresh (sym "A")
     b <- fresh (sym "B")
     funTy <- withEnv (None :> (a, t) :> (b, ret)) $
              eval (CPi x (CVar a) (CVar b))
     return (VNeu (VEq ret from' to')
              (NCong ne (NThe funTy fun)))

doSymm :: Value -> Norm Value
doSymm (VSame v) = return (VSame v)
doSymm (VNeu (VEq t from to) ne) = return (VNeu (VEq t to from) (NSymm ne))


doIndEq :: Value -> Value -> Value -> Norm Value
doIndEq (VSame v) mot base = return base
doIndEq tgt@(VNeu (VEq t from to) ne) mot base =
  do motTo <- doApply mot to
     ty <- doApply motTo tgt
     motFrom <- doApply mot from
     baseTy <- doApply motFrom (VSame from)
     motTy <- indEqMotTy t from
     return (VNeu ty (NIndEq ne (NThe motTy mot) (NThe baseTy base)))

indEqMotTy ty from =
  do p <- fresh (sym "p")
     tN <- fresh (sym "t")
     frN <- fresh (sym "from")
     toN <- fresh (sym "to")
     withEnv (None :> (tN, ty) :> (frN, from)) $
       eval (CPi toN (CVar tN) (CPi p (CEq (CVar tN) (CVar frN) (CVar toN)) CU))

doHead (VVecCons e _) = return e
doHead (VNeu (VVec elem _) ne) = return (VNeu elem (NHead ne))

doTail (VVecCons e _) = return e
doTail (VNeu (VVec elem (VAdd1 k)) ne) = return (VNeu (VVec elem k) (NTail ne))

doIndVec VZero VVecNil mot base step = return base
doIndVec (VAdd1 k) (VVecCons v vs) mot base step =
  do soFar <- doIndVec k vs mot base step
     step1 <- doApply step k
     step2 <- doApply step1 v
     step3 <- doApply step2 vs
     doApply step3 soFar
-- TODO neutral cases


readBack :: Normal -> Norm Core
readBack (NThe VAtom (VTick x)) = return (CTick x)
readBack (NThe VNat  VZero) = return CZero
readBack (NThe VNat (VAdd1 k)) = CAdd1 <$> readBack (NThe VNat k)
readBack (NThe (VPi x dom ran) fun) =
  do y <- fresh x
     let yVal = VNeu dom (NVar y)
     bodyVal <- doApply fun yVal
     bodyType <- instantiate ran x yVal
     CLambda y <$> readBack (NThe bodyType bodyVal)
readBack (NThe (VSigma x aT dT) p) =
  do av <- doCar p
     a <- readBack (NThe aT av)
     dT' <- instantiate dT x av
     dv <- doCdr p
     d <- readBack (NThe dT' dv)
     return (CCons a d)
readBack (NThe VTrivial _) = return CSole
readBack (NThe (VEq ty _ _) (VSame v)) = CSame <$> readBack (NThe ty v)
readBack (NThe (VVec _ _) VVecNil) = return CVecNil
readBack (NThe (VVec elem (VAdd1 len)) (VVecCons v vs)) =
  CVecCons <$> readBack (NThe elem v) <*> readBack (NThe (VVec elem len) vs)
readBack (NThe VU t) = readBackType t
readBack (NThe t (VNeu t' neu)) = readBackNeutral neu

readBackType :: Value -> Norm Core
readBackType VAtom = return CAtom
readBackType VNat = return CNat
readBackType (VPi x dom ran) =
  do y <- fresh x
     ranV <- instantiate ran x (VNeu dom (NVar y))
     CPi y <$> readBackType dom <*> inBound y (readBackType ranV)
readBackType (VSigma x a d) =
  do y <- fresh x
     dV <- instantiate d x (VNeu a (NVar y))
     CSigma y <$> readBackType a <*> inBound y (readBackType dV)
readBackType VTrivial = return CTrivial
readBackType (VEq t from to) =
  CEq <$> readBackType t <*> readBack (NThe t from) <*> readBack (NThe t to)
readBackType (VVec elem len) =
  CVec <$> readBackType elem <*> readBack (NThe VNat len)
readBackType VU = return CU

readBackNeutral :: Neutral -> Norm Core
readBackNeutral (NVar x) = return (CVar x)
readBackNeutral (NIndNat tgt mot base step) =
  CIndNat <$> readBackNeutral tgt <*> readBack mot <*> readBack base <*> readBack step
readBackNeutral (NApp neu arg) = CApp <$> readBackNeutral neu <*> readBack arg
readBackNeutral (NCar p) = CCar <$> readBackNeutral p
readBackNeutral (NCdr p) = CCdr <$> readBackNeutral p
readBackNeutral (NReplace tgt mot base) =
  CReplace <$> readBackNeutral tgt <*> readBack mot <*> readBack base
readBackNeutral (NTrans1 ne no) =
  CTrans <$> readBackNeutral ne <*> readBack no
readBackNeutral (NTrans2 no ne) =
  CTrans <$> readBack no <*> readBackNeutral ne
readBackNeutral (NTrans12 ne1 ne2) =
  CTrans <$> readBackNeutral ne1 <*> readBackNeutral ne2
readBackNeutral (NCong ne fun@(NThe (VPi _ a (Closure e c)) _)) =
  do b <- withEnv e (eval c)
     CCong <$> readBackNeutral ne <*> readBackType b <*> readBack fun
readBackNeutral (NSymm ne) = CSymm <$> readBackNeutral ne
readBackNeutral (NIndEq tgt mot base) =
  CIndEq <$> readBackNeutral tgt <*> readBack mot <*> readBack base
readBackNeutral (NHead ne) = CVecHead <$> readBackNeutral ne
readBackNeutral (NTail ne) = CVecTail <$> readBackNeutral ne

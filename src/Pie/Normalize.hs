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
readBackType VU = return CU

readBackNeutral :: Neutral -> Norm Core
readBackNeutral (NVar x) = return (CVar x)
readBackNeutral (NIndNat tgt mot base step) =
  CIndNat <$> readBackNeutral tgt <*> readBack mot <*> readBack base <*> readBack step
readBackNeutral (NApp neu arg) = CApp <$> readBackNeutral neu <*> readBack arg
readBackNeutral (NCar p) = CCar <$> readBackNeutral p
readBackNeutral (NCdr p) = CCdr <$> readBackNeutral p

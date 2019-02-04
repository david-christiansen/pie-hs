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
eval (CVar x)  = var x
eval (CPi x dom ran) =
  VPi x <$> eval dom <*> close ran
eval (CLambda x body) =
  VLambda x <$> close body
eval (CApp rator rand) =
  do fun <- eval rator
     arg <- eval rand
     apply fun arg
eval CU = return VU

apply :: Value -> Value -> Norm Value
apply (VLambda x clos) arg =
  instantiate clos x arg
apply (VNeu (VPi x a b) f) arg =
  VNeu <$> (instantiate b x arg)
       <*> pure (NApp f (The a arg))
apply other arg = panic ("Not a function: " ++ show other)

readBack :: Normal -> Norm Core
readBack (The VAtom (VTick x)) = return (CTick x)
readBack (The VNat  VZero) = return CZero
readBack (The VNat (VAdd1 k)) = CAdd1 <$> readBack (The VNat k)
readBack (The (VPi x dom ran) fun) =
  do y <- fresh x
     let yVal = VNeu dom (NVar y)
     bodyVal <- apply fun yVal
     bodyType <- instantiate ran x yVal
     CLambda y <$> readBack (The bodyType bodyVal)
readBack (The VU t) = readBackType t
readBack (The t (VNeu t' neu)) = readBackNeutral neu

readBackType :: Value -> Norm Core
readBackType VAtom = return CAtom
readBackType VNat = return CNat
readBackType (VPi x dom ran) =
  do y <- fresh x
     ranV <- instantiate ran x (VNeu dom (NVar y))
     CPi y <$> readBackType dom <*> inBound y (readBackType ranV)

readBackNeutral :: Neutral -> Norm Core
readBackNeutral (NVar x) = return (CVar x)
readBackNeutral (NApp neu arg) = CApp <$> readBackNeutral neu <*> readBack arg

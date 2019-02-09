module Pie.Elab where

import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.Text as T

import Pie.AlphaEquiv
import Pie.Fresh
import qualified Pie.Normalize as Norm
import Pie.Panic
import Pie.Types

data CtxEntry a =
  HasType a

type Ctx a = Bwd (Symbol, CtxEntry a)

names :: Ctx a -> [Symbol]
names None = []
names (ctx :> (x, _)) = x : names ctx

data E = C Core | E (Expr' Expr)
  deriving Show

newtype ElabErr = ElabErr (Located [MessagePart E])
  deriving Show

newtype Elab a =
  Elab
    { runElab ::
        Ctx Value ->
        Loc ->
        [(Symbol, Symbol)] ->
        Either ElabErr a
    }

instance Functor Elab where
  fmap f (Elab act) = Elab (\ ctx loc ren -> fmap f (act ctx loc ren))

instance Applicative Elab where
  pure x = Elab (\ _ _ _ -> (pure x))
  Elab fun <*> Elab arg =
    Elab (\ctx loc ren -> fun ctx loc ren <*> arg ctx loc ren)

instance Monad Elab where
  return = pure
  Elab act >>= f =
    Elab (\ ctx loc ren ->
            case act ctx loc ren of
              Left err -> Left err
              Right v -> runElab (f v) ctx loc ren)

fresh :: Symbol -> Elab Symbol
fresh x =
  do used <- names <$> getCtx
     return (freshen used x)

failure :: [MessagePart E] -> Elab a
failure msg = Elab (\ ctx loc _ -> Left (ElabErr (Located loc msg)))

getCtx :: Elab (Ctx Value)
getCtx = Elab (\ ctx _ _ -> pure ctx)

applyRenaming :: Symbol -> Elab Symbol
applyRenaming x =
  Elab (\ _ _ ren ->
          case lookup x ren of
            Nothing -> panic ("Can't rename " ++ show x)
            Just y -> pure y)

rename :: Symbol -> Symbol -> Elab a -> Elab a
rename from to (Elab act) =
  Elab (\ ctx loc ren -> act ctx loc ((from, to) : ren))

withModifiedCtx :: (Ctx Value -> Ctx Value) -> Elab a -> Elab a
withModifiedCtx f (Elab act) =
  Elab (\ctx loc ren -> act (f ctx) loc ren)

withCtxExtension :: Symbol -> Value -> Elab a -> Elab a
withCtxExtension x t = withModifiedCtx (:> (x, HasType t))

toEnv None = None
toEnv (ctx :> (x, HasType t)) =
  toEnv ctx :> (x, VNeu t (NVar x))

runNorm :: Norm.Norm a -> Elab a
runNorm n =
  do usedNames <- names <$> getCtx
     initEnv <- toEnv <$> getCtx
     let val = Norm.runNormalize n usedNames initEnv
     return val


eval :: Core -> Elab Value
eval = runNorm . Norm.eval

evalInEnv :: Env Value -> Core -> Elab Value
evalInEnv env c =
  do usedNames <- names <$> getCtx
     return (Norm.runNormalize (Norm.eval c) usedNames env)


doCar :: Value -> Elab Value
doCar = runNorm . Norm.doCar

doApply :: Value -> Value -> Elab Value
doApply fun arg = runNorm (Norm.doApply fun arg)


close :: Core -> Elab (Closure Value)
close e =
  do env <- toEnv <$> getCtx
     return (Closure env e)

instantiate :: Closure Value -> Symbol -> Value -> Elab Value
instantiate clos x v = runNorm (Norm.instantiate clos x v)

readBackType :: Value -> Elab Core
readBackType = runNorm . Norm.readBackType

readBack :: Normal -> Elab Core
readBack = runNorm . Norm.readBack



inExpr :: Expr -> ((Expr' Expr) -> Elab a) -> Elab a
inExpr (Expr (Located loc e)) act =
  Elab (\ ctx _ ren ->
          runElab (act e) ctx loc ren)

isType :: Expr -> Elab Core
isType e = inExpr e isType'

isType' :: (Expr' Expr) -> Elab Core
isType' U = pure CU
isType' Nat = pure CNat
isType' Atom = pure CAtom
isType' (Arrow dom (t:|ts)) =
  do x <- fresh (Symbol (T.pack "x"))
     dom' <- isType dom
     domVal <- eval dom'
     ran' <- withCtxExtension x domVal $
             case ts of
               [] ->
                 isType t
               (ty : tys) ->
                 isType' (Arrow t (ty :| tys))
     return (CPi x dom' ran')
isType' (Pi ((x, dom) :| doms) ran) =
  do dom' <- isType dom
     domVal <- eval dom'
     ran' <- withCtxExtension x domVal $
             case doms of
               [] ->
                 isType ran
               ((y, d) : ds) ->
                 isType' (Pi ((y, d) :| ds) ran)
     return (CPi x dom' ran')
isType' (Pair a d) =
  do x <- fresh (Symbol (T.pack "x"))
     a' <- isType a
     aVal <- eval a'
     d' <- withCtxExtension x aVal $ isType d
     return (CSigma x a' d')
isType' (Sigma ((x, a) :| as) d) =
  do a' <- isType a
     aVal <- eval a'
     d' <- withCtxExtension x aVal $
             case as of
               [] ->
                 isType d
               ((y, d) : ds) ->
                 isType' (Sigma ((y, d) :| ds) d)
     return (CSigma x a' d')
isType' Trivial = return CTrivial
isType' (Eq t from to) =
  do t' <- isType t
     tV <- eval t'
     CEq t' <$> check tV from <*> check tV to
isType' other = failure [MText (T.pack "Not a type"), MVal (E other)]


data SynthResult = SThe { theType :: Value, theExpr :: Core }
  deriving Show

toplevel e =
  do (SThe tv e') <- synth e
     t <- readBackType tv
     val <- eval e'
     eN <- readBack (NThe tv val)
     return (CThe t eN)

synth e = inExpr e synth'

synth' (Tick x) = pure (SThe VAtom (CTick x)) -- TODO check validity of x
synth' Atom = pure (SThe VU CAtom)
synth' Zero = pure (SThe VNat CZero)
synth' (Add1 n) =
  do n' <- check VNat n
     return (SThe VNat (CAdd1 n'))
synth' (IndNat tgt mot base step) =
  do tgt' <- check VNat tgt
     k <- fresh (sym "k")
     mot' <- check (VPi k VNat (Closure None CU)) mot
     motV <- eval mot'
     baseT <- doApply motV VZero
     base' <- check baseT base
     soFar <- fresh (sym "so-far")
     stepT <- let motName = Symbol (T.pack "mot")
              in evalInEnv
                   (None :> (motName, motV))
                   (CPi k CNat
                     (CPi soFar (CApp (CVar motName) (CVar k))
                       (CApp (CVar motName) (CAdd1 (CVar k)))))
     step' <- check stepT step
     tgtV <- eval tgt'
     ty <- doApply motV tgtV
     return (SThe ty (CIndNat tgt' mot' base' step'))
synth' Nat = pure (SThe VU CNat)
synth' (Var x) =
  do ctx <- getCtx
     x' <- applyRenaming x
     findVar x' ctx
  where
    findVar x' None = failure [MText (T.pack "Unknown variable"), MVal (E (Var x))]
    findVar x' (ctx' :> (y, HasType t))
      | x' == y = pure (SThe t (CVar x'))
      | otherwise = findVar x' ctx'
synth' (Arrow dom (t:|ts)) =
  do x <- fresh (Symbol (T.pack "x"))
     dom' <- check VU  dom
     domVal <- eval dom'
     ran' <- withCtxExtension x domVal $
             case ts of
               [] ->
                 check VU t
               (ty : tys) ->
                 check' VU (Arrow t (ty :| tys))
     return (SThe VU (CPi x dom' ran'))
synth' (Pi ((x, dom) :| doms) ran) =
  do dom' <- check VU dom
     domVal <- eval dom'
     ran' <- withCtxExtension x domVal $
             case doms of
               [] ->
                 check VU ran
               ((y, d) : ds) ->
                 check' VU (Pi ((y, d) :| ds) ran)
     return (SThe VU (CPi x dom' ran'))
synth' (Sigma ((x, a) :| as) d) =
  do a' <- check VU a
     aVal <- eval a'
     d' <- withCtxExtension x aVal $
             case as of
               [] ->
                 check VU d
               ((y, d) : ds) ->
                 check' VU (Pi ((y, d) :| ds) d)
     return (SThe VU (CSigma x a' d'))
synth' (Pair a d) =
  do a' <- check VU a
     aVal <- eval a'
     x <- fresh (sym "a")
     d' <- withCtxExtension x aVal $ check VU d
     return (SThe VU (CSigma x a' d'))
synth' (Car p) =
  do SThe ty p' <- synth p
     case ty of
       VSigma x aT dT ->
         return (SThe aT (CCar p'))
       other ->
         do ty <- readBackType other
            failure [MText (T.pack "Not a Σ: "), MVal (C ty)]
synth' (Cdr p) =
  do SThe ty p' <- synth p
     case ty of
       VSigma x aT dT ->
         do a <- eval p' >>= doCar
            dV <- instantiate dT x a
            return (SThe dV (CCar p'))
       other ->
         do ty <- readBackType other
            failure [MText (T.pack "Not a Σ: "), MVal (C ty)]
synth' Trivial = return (SThe VU CTrivial)
synth' Sole = return (SThe VTrivial CSole)
synth' (The ty e) =
  do ty' <- isType ty
     tv <- eval ty'
     e' <- check tv e
     return (SThe tv e')
synth' (App rator rand1 rands) =
  do (SThe ratorT rator') <- synth rator
     checkArgs rator' ratorT (rand1 :| rands)

  where
    checkArgs fun (VPi x dom ran) (rand1 :| rands) =
      do rand1' <- check dom rand1
         rand1v <- eval rand1'
         exprTy <- instantiate ran x rand1v
         case rands of
           [] -> return (SThe exprTy (CApp fun rand1'))
           (r:rs) -> checkArgs (CApp fun rand1') exprTy (r :| rs)
    checkArgs _ other _ =
      do t <- readBackType other
         failure [MText (T.pack "Not a Π type: "), MVal (C t)]
synth' other = failure [ MText (T.pack "Can't synth")
                       , MVal (E other)
                       ]

check :: Value -> Expr -> Elab Core
check t e = inExpr e (check' t)

check' t (Lambda (x :| xs) body) =
  case t of
    VPi y dom ran ->
      do z <- fresh y
         withCtxExtension z dom $
           do bodyT <- instantiate ran y (VNeu dom (NVar z))
              case xs of
                [] ->
                  do body' <- rename x z $
                              check bodyT body
                     return (CLambda z body')
                (y:ys) ->
                  do body' <- rename x z $
                              check' bodyT (Lambda (y :| ys) body)
                     return (CLambda z body')
    other ->
      do t' <- readBackType other
         failure [MText (T.pack "Not a function type"), MVal (C t')]
check' t (Cons a d) =
  case t of
    VSigma x aT dT ->
      do a' <- check aT a
         av <- eval a'
         dT' <- instantiate dT x av
         d' <- check dT' d
         return (CCons a' d')
    other ->
      do t' <- readBackType other
         failure [MText (T.pack "Not a pair type"), MVal (C t')]
check' t (Same e) =
  case t of
    VEq ty from to ->
      do e' <- check ty e
         v <- eval e'
         same ty from v
         same ty v to
         return (CSame e')
         
    other ->
      do t' <- readBackType other
         failure [MText (T.pack "Not an equality type"), MVal (C t')]      
check' t other =
  do SThe t' other' <- synth' other
     sameType t t'
     return other'

same ty v1 v2 =
  do c1 <- readBack (NThe ty v1)
     c2 <- readBack (NThe ty v2)
     case alphaEquiv c1 c2 of
       Left reason ->
         do t <- readBackType ty
         -- TODO include specific reason as well
            failure [ MVal (C c1)
                    , MText (T.pack "is not the same")
                    , MVal (C t)
                    , MText (T.pack "as")
                    , MVal (C c2)
                    ]
       Right _ -> pure ()

sameType v1 v2 =
  do c1 <- readBackType v1
     c2 <- readBackType v2
     case alphaEquiv c1 c2 of
       Left reason ->
         -- TODO include specific reason as well
         failure [ MVal (C c1)
                 , MText (T.pack "is not the same type as")
                 , MVal (C c2)
                 ]
       Right _ -> pure ()

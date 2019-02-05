module Pie.Elab where

import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.Text as T

import Pie.AlphaEquiv
import qualified Pie.Normalize as Norm
import Pie.Types

data CtxEntry a =
  HasType a

type Ctx a = Bwd (Symbol, CtxEntry a)

names :: Ctx a -> [Symbol]
names None = []
names (ctx :> (x, _)) = x : names ctx

data E = C Core | E Expr'
  deriving Show

newtype ElabErr = ElabErr (Located [MessagePart E])
  deriving Show

newtype Elab a =
  Elab
    { runElab ::
        Ctx Value ->
        Loc ->
        Either ElabErr a
    }

instance Functor Elab where
  fmap f (Elab act) = Elab (\ ctx loc -> fmap f (act ctx loc))

instance Applicative Elab where
  pure x = Elab (\ _ _ -> (pure x))
  Elab fun <*> Elab arg =
    Elab (\ctx loc -> fun ctx loc <*> arg ctx loc)

instance Monad Elab where
  return = pure
  Elab act >>= f =
    Elab (\ ctx loc ->
            case act ctx loc of
              Left err -> Left err
              Right v -> runElab (f v) ctx loc)

failure :: [MessagePart E] -> Elab a
failure msg = Elab (\ ctx loc -> Left (ElabErr (Located loc msg)))

getCtx :: Elab (Ctx Value)
getCtx = Elab (\ ctx _ -> pure ctx)

withModifiedCtx :: (Ctx Value -> Ctx Value) -> Elab a -> Elab a
withModifiedCtx f (Elab act) =
  Elab (\ctx loc -> act (f ctx) loc)

withCtxExtension :: Symbol -> Value -> Elab a -> Elab a
withCtxExtension x t = withModifiedCtx (:> (x, HasType t))

toEnv None = None
toEnv (ctx :> (x, HasType t)) =
  toEnv ctx :> (x, VNeu t (NVar x))

eval :: Core -> Elab Value
eval c =
  do usedNames <- names <$> getCtx
     initEnv <- toEnv <$> getCtx
     let val = Norm.runNormalize (Norm.eval c) usedNames initEnv
     return val

readBackType :: Value -> Elab Core
readBackType v =
  do usedNames <- names <$> getCtx
     initEnv <- toEnv <$> getCtx
     let t = Norm.runNormalize (Norm.readBackType v) usedNames initEnv
     return t


inExpr :: Expr -> (Expr' -> Elab a) -> Elab a
inExpr (Expr (Located loc e)) act =
  Elab (\ ctx _ ->
          runElab (act e) ctx loc)

isType :: Expr -> Elab Core
isType e = inExpr e isType'

isType' :: Expr' -> Elab Core
isType' U = pure CU
isType' Nat = pure CNat
isType' Atom = pure CAtom
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
isType' other = failure [MText (T.pack "Not a type"), MVal (E other)]


data SynthResult = SThe { theType :: Core, theExpr :: Core }
  deriving Show

synth e = inExpr e synth'

synth' (Tick x) = pure (SThe CAtom (CTick x)) -- TODO check validity of x
synth' Atom = pure (SThe CU CAtom)
synth' Zero = pure (SThe CNat CZero)
synth' (Add1 n) =
  do n' <- check CNat n
     return (SThe CNat (CAdd1 n'))
synth' Nat = pure (SThe CU CNat)
synth' (Var x) =
  do ctx <- getCtx
     findVar ctx
  where
    findVar None = failure [MText (T.pack "Unknown variable"), MVal (E (Var x))]
    findVar (ctx' :> (y, HasType t))
      | x == y =
        do t' <- readBackType t
           pure (SThe t' (CVar x))
      | otherwise = findVar ctx'
synth' (Pi ((x, dom) :| doms) ran) =
  do dom' <- check CU dom
     domVal <- eval dom'
     ran' <- withCtxExtension x domVal $
             case doms of
               [] ->
                 check CU ran
               ((y, d) : ds) ->
                 check' CU (Pi ((y, d) :| ds) ran)
     return (SThe CU (CPi x dom' ran'))
synth' (The ty e) =
  do ty' <- isType ty
     e' <- check ty' e
     return (SThe ty' e')
synth' (App rator rand1 rands) = error "TODO"
synth' other = failure [ MText (T.pack "Can't synth")
                       , MVal (E other)
                       ]

check t e = inExpr e (check' t)

check' t (Lambda [x] body) =
  case t of
    CPi y dom ran ->
      error "TODO"
    other ->
      failure [MText (T.pack "Not a function type"), MVal (C other)]
check' t other =
  do SThe t' other' <- synth' other
     sameType t t'
     return other'

-- TODO make caller evaluate args
sameType e1 e2 =
  do v1 <- eval e1
     v2 <- eval e2
     c1 <- readBackType v1
     c2 <- readBackType v2
     case alphaEquiv c1 c2 of
       Left reason ->
         -- TODO include specific reason as well
         failure [ MVal (C e1)
                 , MText (T.pack "is not the same type as")
                 , MVal (C e2)
                 ]
       Right _ -> pure ()

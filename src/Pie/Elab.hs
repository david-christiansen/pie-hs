module Pie.Elab where

import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.Text as T

import qualified Pie.Normalize as Norm
import Pie.Types

data CtxEntry a =
  HasType a

type Ctx a = Bwd (Symbol, CtxEntry a)

names :: Ctx a -> [Symbol]
names None = []
names (ctx :> (x, _)) = x : names ctx

newtype ElabErr = ElabErr (Located [MessagePart Expr'])
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

failure :: [MessagePart Expr'] -> Elab a
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
isType' other = failure [MText (T.pack "Not a type"), MVal other]



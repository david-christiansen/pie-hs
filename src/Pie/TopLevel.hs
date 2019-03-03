module Pie.TopLevel where

import qualified Data.Text as T

import Pie.Elab (Ctx, CtxEntry(..), Elab)
import qualified Pie.Elab as E
import Pie.Fresh
import Pie.Normalize (Norm)
import qualified Pie.Normalize as N
import Pie.Types

data TopState = TopState { topCtx :: Ctx Value
                         , topRename :: [(Symbol, Symbol)]
                         }
  deriving Show

newtype TopElab a =
  TopElab
    { runTopElab ::
        TopState ->
        Loc ->
        ([Located ElabInfo], Either ElabErr (a, TopState))
    }

instance Functor TopElab where
  fmap f (TopElab act) =
    TopElab (\st loc ->
               let (info, res) = act st loc
               in case res of
                    Left err -> (info, Left err)
                    Right (v, st') -> (info, Right (f v, st')))

instance Applicative TopElab where
  pure x = TopElab (\st loc -> ([], Right (x, st)))
  TopElab fun <*> TopElab arg =
    TopElab (\st loc ->
               let (info1, res1) = fun st loc
               in case res1 of
                    Left err -> (info1, Left err)
                    Right (f, st') ->
                      let (info2, res2) = arg st' loc
                      in (info1 ++ info2,
                          case res2 of
                            Left err -> Left err
                            Right (v, st'') -> Right (f v, st'')))

instance Monad TopElab where
  return = pure
  TopElab act1 >>= f =
    TopElab (\st loc ->
               let (info1, res1) = act1 st loc
               in case res1 of
                    Left err -> (info1, Left err)
                    Right (v, st') ->
                      let TopElab act2 = f v
                          (info2, res2) = act2 st' loc
                      in (info1 ++ info2, res2))

get :: TopElab TopState
get = TopElab (\st _ -> ([], Right (st, st)))

modify :: (TopState -> TopState) -> TopElab ()
modify f = TopElab (\st _ -> ([], Right ((), f st)))

fresh :: Symbol -> TopElab Symbol
fresh x =
  do used <- E.names . topCtx <$> get
     return (freshen used x)

withCurrentLoc :: Loc -> TopElab a -> TopElab a
withCurrentLoc loc (TopElab act) =
  TopElab (\st _ -> act st loc)

currentLoc :: TopElab Loc
currentLoc = TopElab (\st loc -> ([], Right (loc, st)))

tellInfo :: [Located ElabInfo] -> TopElab ()
tellInfo info = TopElab (\st _ -> (info, Right ((), st)))

failure :: ElabErr -> TopElab a
failure err = TopElab (\st _ -> ([], Left err))

runNorm :: Norm a -> TopElab a
runNorm act =
  do ctx <- topCtx <$> get
     let used = E.names ctx
         env = E.toEnv ctx
     return (N.runNorm act used env)

runElab :: Elab a -> TopElab a
runElab act =
  do st <- get
     loc <- currentLoc
     let ctx = topCtx st
         ren = topRename st
         (info, res) = E.runElab act ctx loc ren
     tellInfo info
     case res of
       Left err -> failure err
       Right v -> pure v

runElabErr :: Elab a -> TopElab ([Located ElabInfo], Either ElabErr a)
runElabErr act =
  do st <- get
     loc <- currentLoc
     let ctx = topCtx st
         ren = topRename st
         (info, res) = E.runElab act ctx loc ren
     return (info, res)


-- TODO prevent double claims
addClaim :: Symbol -> Loc -> Value -> TopElab ()
addClaim x loc ty =
  TopElab (\st _ ->
             let ctx = topCtx st
             in ([], Right ((), st { topCtx = ctx :> (x, Claimed loc ty) })))

rename :: Symbol -> TopElab Symbol
rename x =
  do ren <- topRename <$> get
     tryRename ren
  where
    tryRename [] =
      do loc <- currentLoc
         failure (ElabErr (Located loc [MText (T.pack "Not claimed")]))
    tryRename ((y, y') : ren)
      | x == y = pure y'
      | otherwise = tryRename ren


getClaim :: Symbol -> TopElab Value
getClaim x =
  do st <- get
     let ren = topRename st
         ctx = topCtx st
     x' <- rename x
     loc <- currentLoc
     find loc x' ctx []

  where

    find loc x' None _ =
      failure (ElabErr (Located loc [MText (T.pack "Missing claim")]))
    find loc x' (inCtx :> elem@(y, info)) seen
      | x' == y =
        case info of
          Claimed cloc ty ->
            do tellInfo [Located loc (ClaimAt cloc)]
               modify (\st -> st { topCtx = restore inCtx seen })
               return ty
          _ ->
            failure (ElabErr (Located loc [MText (T.pack "Not claimed")]))
      | otherwise = find loc x' inCtx (elem : seen)


    restore :: Bwd a -> [a] -> Bwd a
    restore xs [] = xs
    restore xs (y:ys) = restore (xs :> y) ys

addDef :: Symbol -> Loc -> Value -> Value -> TopElab ()
addDef x loc ty def =
  TopElab (\st _ ->
             let ctx = topCtx st
             in ([], Right ((), st { topCtx = ctx :> (x, Defined loc ty def) })))

addRename :: Symbol -> Symbol -> TopElab ()
addRename x x' = modify (\st -> st { topRename = (x, x') : topRename st })

top :: Located (TopLevel Expr) -> TopElab ()
top (Located loc t) = withCurrentLoc loc (top' t)

top' (Claim (Located xloc x) ty) =
  do cTy <- runElab (E.isType ty)
     vTy <- runNorm (N.eval cTy)
     x' <- fresh x
     addClaim x' xloc vTy
     addRename x x'
top' (Define (Located xloc x) def) =
  do ty <- getClaim x
     cDef <- runElab (E.check ty def)
     vDef <- runNorm (N.eval cDef)
     x' <- rename x
     addDef x' xloc ty vDef
top' (CheckSame ty e1 e2) =
  do cTy <- runElab (E.isType ty)
     vTy <- runNorm (N.eval cTy)
     c1 <- runElab (E.check vTy e1)
     v1 <- runNorm (N.eval c1)
     c2 <- runElab (E.check vTy e2)
     v2 <- runNorm (N.eval c2)
     runElab (E.same vTy v1 v2)
top' (Example expr) =
  do (sInfo, sRes) <- runElabErr (E.synth expr)
     case sRes of
       Right (E.SThe vTy cExpr) ->
         do tellInfo sInfo
            vExpr <- runNorm (N.eval cExpr)
            nTy <- runNorm (N.readBackType vTy)
            nExpr <- runNorm (N.readBack (NThe vTy vExpr))
            loc <- currentLoc
            tellInfo [Located loc (ExampleOut (CThe nTy nExpr))]
       Left err ->
         do (tInfo, tRes) <- runElabErr (E.isType expr)
            case tRes of
              Left _ ->
                do tellInfo sInfo
                   failure err
              Right ty ->
                do tellInfo tInfo
                   vTy <- runNorm (N.eval ty)
                   nTy <- runNorm (N.readBackType vTy)
                   loc <- currentLoc
                   tellInfo [Located loc (ExampleOut nTy)]

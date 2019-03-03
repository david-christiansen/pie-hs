module Pie.Elab where

import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.Text as T

import Pie.AlphaEquiv
import Pie.Fresh
import qualified Pie.Normalize as Norm
import Pie.Panic
import Pie.Types

data CtxEntry a = HasType (Maybe Loc) a
                | Claimed Loc a
                | Defined Loc a a -- ^ type then value
  deriving Show

entryType (HasType _ t) = t
entryType (Defined _ t _) = t
entryType (Claimed _ t) = t

inScope :: CtxEntry a -> Bool
inScope (Claimed _ _) = False
inScope _ = True

type Ctx a = Bwd (Symbol, CtxEntry a)

names :: Ctx a -> [Symbol]
names None = []
names (ctx :> (x, _)) = x : names ctx

data E = C Core | E Expr
  deriving Show

newtype ElabErr = ElabErr (Located [MessagePart E])
  deriving Show


newtype Elab a =
  Elab
    { runElab ::
        Ctx Value ->
        Loc ->
        [(Symbol, Symbol)] ->
        ([Located ElabInfo], Either ElabErr a)
    }

instance Functor Elab where
  fmap f (Elab act) =
    Elab (\ ctx loc ren ->
            let (info, out) = act ctx loc ren
            in (info, fmap f out))

instance Applicative Elab where
  pure x = Elab (\ _ _ _ -> ([], pure x))
  Elab fun <*> Elab arg =
    Elab (\ctx loc ren ->
            let (funInfo, theFun) = fun ctx loc ren
                (argInfo, theArg) = arg ctx loc ren
            in (funInfo ++ argInfo, theFun <*> theArg))

instance Monad Elab where
  return = pure
  Elab act >>= f =
    Elab (\ ctx loc ren ->
            case act ctx loc ren of
              (info, Left err) -> (info, Left err)
              (info, Right v)  ->
                let (moreInfo, val) = runElab (f v) ctx loc ren
                in (info ++ moreInfo, val))

logInfo :: ElabInfo -> Elab ()
logInfo info = Elab (\_ loc _ -> ([Located loc info], pure ()))

fresh :: Symbol -> Elab Symbol
fresh x =
  do used <- names <$> getCtx
     return (freshen used x)

failure :: [MessagePart E] -> Elab a
failure msg = Elab (\ ctx loc _ -> ([], Left (ElabErr (Located loc msg))))

getCtx :: Elab (Ctx Value)
getCtx = Elab (\ ctx _ _ -> ([], pure ctx))

currentLoc :: Elab Loc
currentLoc = Elab (\_ loc _ -> ([], pure loc))

applyRenaming :: Symbol -> Elab Symbol
applyRenaming x =
  Elab (\ _ loc ren ->
          case lookup x ren of
            Nothing -> ([], Left (ElabErr (Located loc [MText (T.pack ("Unknown variable " ++ show x ++ " in " ++ show ren))])))
            Just y -> ([], pure y))

rename :: Symbol -> Symbol -> Elab a -> Elab a
rename from to (Elab act) =
  Elab (\ ctx loc ren -> act ctx loc ((from, to) : ren))

withModifiedCtx :: (Ctx Value -> Ctx Value) -> Elab a -> Elab a
withModifiedCtx f (Elab act) =
  Elab (\ctx loc ren -> act (f ctx) loc ren)

withCtxExtension :: Symbol -> Maybe Loc -> Value -> Elab a -> Elab a
withCtxExtension x loc t = withModifiedCtx (:> (x, HasType loc t))

toEnv None = None
toEnv (ctx :> (x, HasType _ t)) =
  toEnv ctx :> (x, VNeu t (NVar x))
toEnv (ctx :> (x, Defined _ _ d)) =
  toEnv ctx :> (x, d)
toEnv (ctx :> (_, Claimed _ _)) =
  toEnv ctx

runNorm :: Norm.Norm a -> Elab a
runNorm n =
  do usedNames <- names <$> getCtx
     initEnv <- toEnv <$> getCtx
     let val = Norm.runNorm n usedNames initEnv
     return val


eval :: Core -> Elab Value
eval = runNorm . Norm.eval

evalInEnv :: Env Value -> Core -> Elab Value
evalInEnv env c =
  do usedNames <- names <$> getCtx
     return (Norm.runNorm (Norm.eval c) usedNames env)


doCar :: Value -> Elab Value
doCar = runNorm . Norm.doCar

doApply :: Value -> Value -> Elab Value
doApply fun arg = runNorm (Norm.doApply fun arg)

doApplyMany :: Value -> [Value] -> Elab Value
doApplyMany fun args = runNorm (Norm.doApplyMany fun args)


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



inExpr :: Expr -> ((Expr' Loc) -> Elab a) -> Elab a
inExpr (Expr loc e) act =
  Elab (\ ctx _ ren ->
          runElab (act e) ctx loc ren)

isType :: Expr -> Elab Core
isType e =
  do res <- inExpr e isType'
     inExpr e (const (logInfo ExprIsType))
     return res

isType' :: (Expr' Loc) -> Elab Core
isType' U = pure CU
isType' Nat = pure CNat
isType' Atom = pure CAtom
isType' (Arrow dom (t:|ts)) =
  do x <- fresh (Symbol (T.pack "x"))
     dom' <- isType dom
     domVal <- eval dom'
     ran' <- withCtxExtension x Nothing domVal $
             case ts of
               [] ->
                 isType t
               (ty : tys) ->
                 isType' (Arrow t (ty :| tys))
     return (CPi x dom' ran')
isType' (Pi ((loc, x, dom) :| doms) ran) =
  do dom' <- isType dom
     domVal <- eval dom'
     x' <- fresh x
     ran' <- withCtxExtension x' (Just loc) domVal $
             rename x x' $
             case doms of
               [] ->
                 isType ran
               (nextArg : ds) ->
                 isType' (Pi (nextArg :| ds) ran)
     return (CPi x' dom' ran')
isType' (Pair a d) =
  do x <- fresh (Symbol (T.pack "x"))
     a' <- isType a
     aVal <- eval a'
     d' <- withCtxExtension x Nothing aVal $ isType d
     return (CSigma x a' d')
isType' (Sigma ((loc, x, a) :| as) d) =
  do a' <- isType a
     aVal <- eval a'
     x' <- fresh x
     d' <- withCtxExtension x (Just loc) aVal $
           rename x x' $
             case as of
               [] ->
                 isType d
               (nextA : ds) ->
                 isType' (Sigma (nextA :| ds) d)
     return (CSigma x' a' d')
isType' Trivial = return CTrivial
isType' (Eq t from to) =
  do t' <- isType t
     tV <- eval t'
     CEq t' <$> check tV from <*> check tV to
isType' (Vec t len) = CVec <$> isType t <*> check VNat len
isType' (List elem) = CList <$> isType elem
isType' (Either l r) = CEither <$> isType l <*> isType r
isType' Absurd = return CAbsurd
isType' other = check' VU other


data SynthResult = SThe { theType :: Value, theExpr :: Core }
  deriving Show

toplevel e =
  do (SThe tv e') <- synth e
     t <- readBackType tv
     val <- eval e'
     eN <- readBack (NThe tv val)
     return (CThe t eN)

synth :: Expr -> Elab SynthResult
synth e =
  do res@(SThe tv _) <- inExpr e synth'
     t <- readBackType tv
     inExpr e (const (logInfo (ExprHasType t)))
     return res

synth' (Tick x) = pure (SThe VAtom (CTick x)) -- TODO check validity of x
synth' Atom = pure (SThe VU CAtom)
synth' Zero = pure (SThe VNat CZero)
synth' (Add1 n) =
  do n' <- check VNat n
     return (SThe VNat (CAdd1 n'))
synth' (NatLit n)
  | n <= 0 = synth' Zero
  | otherwise =
    do loc <- currentLoc
       synth' (Add1 (Expr loc (NatLit (n - 1))))
synth' (WhichNat tgt base step) =
  do tgt' <- check VNat tgt
     SThe bt base' <- synth base
     btName <- fresh (sym "base-type")
     k <- fresh (sym "k")
     stepT <- evalInEnv (None :> (btName, bt)) (CPi k CNat (CVar btName))
     step' <- check stepT step
     bt' <- readBackType bt
     return (SThe bt (CWhichNat tgt' bt' base' step'))
synth' (IterNat tgt base step) =
  do tgt' <- check VNat tgt
     SThe bt base' <- synth base
     btName <- fresh (sym "base-type")
     soFar <- fresh (sym "so-far")
     stepT <- evalInEnv
                (None :> (btName, bt))
                (CPi soFar (CVar btName) (CVar btName))
     step' <- check stepT step
     bt' <- readBackType bt
     return (SThe bt (CIterNat tgt' bt' base' step'))
synth' (RecNat tgt base step) =
  do tgt' <- check VNat tgt
     k <- fresh (sym "k")
     SThe bt base' <- synth base
     soFar <- fresh (sym "so-far")
     btName <- fresh (sym "base-type")
     stepT <- evalInEnv
                (None :> (btName, bt))
                (CPi k CNat
                  (CPi soFar (CVar btName)
                    (CVar btName)))
     step' <- check stepT step
     bt' <- readBackType bt
     return (SThe bt (CRecNat tgt' bt' base' step'))
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
    findVar x' None =
      do loc <- currentLoc
         failure [MText (T.pack "Unknown variable"), MVal (E (Expr loc (Var x)))]
    findVar x' (ctx' :> (y, info))
      | x' == y =
         pure (SThe (entryType info) (CVar x'))
      | otherwise = findVar x' ctx'
synth' (Arrow dom (t:|ts)) =
  do x <- fresh (Symbol (T.pack "x"))
     dom' <- check VU  dom
     domVal <- eval dom'
     ran' <- withCtxExtension x Nothing domVal $
             case ts of
               [] ->
                 check VU t
               (ty : tys) ->
                 check' VU (Arrow t (ty :| tys))
     return (SThe VU (CPi x dom' ran'))
synth' (Pi ((loc, x, dom) :| doms) ran) =
  do dom' <- check VU dom
     domVal <- eval dom'
     x' <- fresh x
     ran' <- rename x x' $ withCtxExtension x' (Just loc) domVal $
             case doms of
               [] ->
                 check VU ran
               (y : ds) ->
                 check' VU (Pi (y :| ds) ran)
     return (SThe VU (CPi x' dom' ran'))
synth' (Sigma ((loc, x, a) :| as) d) =
  do a' <- check VU a
     aVal <- eval a'
     x' <- fresh x
     d' <- withCtxExtension x (Just loc) aVal $
             rename x x' $
             case as of
               [] ->
                 check VU d
               ((loc, y, d) : ds) ->
                 check' VU (Pi ((loc, y, d) :| ds) d)
     return (SThe VU (CSigma x a' d'))
synth' (Pair a d) =
  do a' <- check VU a
     aVal <- eval a'
     x <- fresh (sym "a")
     d' <- withCtxExtension x Nothing aVal $ check VU d
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
synth' (Eq ty from to) =
  do ty' <- check VU ty
     tv <- eval ty'
     from' <- check tv from
     to' <- check tv to
     return (SThe VU (CEq ty' from' to'))
synth' (Cong tgt fun) =
  do SThe tgtT tgt' <- synth tgt
     SThe funT fun' <- synth fun
     case tgtT of
       VEq ty from to ->
         case funT of
           VPi x dom ran ->
             do sameType ty dom
                ran' <- instantiate ran x from
                funV <- eval fun'
                newFrom <- doApply funV from
                newTo <- doApply funV to
                ty' <- readBackType ran'
                return (SThe (VEq ran' newFrom newTo) (CCong tgt' ty' fun'))
           other ->
             do t <- readBackType other
                failure [MText (T.pack "Not an -> type: "), MVal (C t)]
       other ->
         do t <- readBackType other
            failure [MText (T.pack "Not an = type: "), MVal (C t)]
synth' (Replace tgt mot base) =
  do SThe tgtT tgt' <- synth tgt
     case tgtT of
       VEq a from to ->
         do motT <- evalInEnv (None :> (sym "A", a))
                      (CPi (sym "x") (CVar (sym "A"))
                        CU)
            mot' <- check motT mot
            motv <- eval mot'
            baseT <- doApply motv from
            base' <- check baseT base
            ty <- doApply motv to
            return (SThe ty (CReplace tgt' mot' base'))
       other ->
         do t <- readBackType other
            failure [MText (T.pack "Not an = type: "), MVal (C t)]
synth' (Symm tgt) =
  do SThe tgtT tgt' <- synth tgt
     case tgtT of
       VEq a from to ->
         return (SThe (VEq a to from) (CSymm tgt'))
       other ->
         do t <- readBackType other
            failure [MText (T.pack "Not an = type: "), MVal (C t)]
synth' (The ty e) =
  do ty' <- isType ty
     tv <- eval ty'
     e' <- check tv e
     return (SThe tv e')
synth' (App rator (rand1 :| rands)) =
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
synth' (List elem) =
  do elem' <- check VU elem
     return (SThe VU (CList elem'))
synth' (ListCons e es) =
  do SThe t e' <- synth e
     es' <- check (VList t) es
     return (SThe (VList t) (CListCons e' es'))
synth' (RecList tgt base step) =
  do SThe lstT tgt' <- synth tgt
     case lstT of
       VList elem ->
         do (SThe bt base') <- synth base
            stepT <- evalInEnv
                       (None :> (sym "E", elem) :> (sym "base-type", bt))
                       (CPi (sym "e") (CVar (sym "E"))
                         (CPi (sym "es") (CList (CVar (sym "E")))
                           (CPi (sym "so-far") (CVar (sym "base-type"))
                             (CVar (sym "base-type")))))
            step' <- check stepT step
            bt' <- readBackType bt
            return (SThe bt (CRecList tgt' bt' base' step'))
       other ->
         do t <- readBackType other
            failure [MText (T.pack "Not a List type: "), MVal (C t)]
synth' (IndList tgt mot base step) =
  do SThe lstT tgt' <- synth tgt
     case lstT of
       VList elem ->
         do motT <- evalInEnv (None :> (sym "E", elem))
                       (CPi (sym "es") (CList (CVar (sym "E"))) CU)
            mot' <- check motT mot
            motV <- eval mot'
            baseT <- evalInEnv
                       (None :> (sym "mot", motV))
                       (CApp (CVar (sym "mot")) CListNil)
            base' <- check baseT base
            stepT <- evalInEnv
                       (None :> (sym "E", elem) :> (sym "mot", motV))
                       (CPi (sym "e") (CVar (sym "E"))
                         (CPi (sym "es") (CList (CVar (sym "E")))
                           (CPi (sym "so-far") (CApp (CVar (sym "mot"))
                                                     (CVar (sym "es")))
                             (CApp (CVar (sym "mot"))
                                   (CListCons (CVar (sym "e"))
                                              (CVar (sym "es")))))))
            step' <- check stepT step
            tgtV <- eval tgt'
            ty <- doApply motV tgtV
            return (SThe ty (CIndList tgt' mot' base' step'))
       other ->
         do t <- readBackType other
            failure [MText (T.pack "Not a List type: "), MVal (C t)]
synth' (Vec elem len) =
  SThe VU <$> (CVec <$> check VU elem <*> check VNat len)
synth' (VecHead es) =
  do SThe esT es' <- synth es
     case esT of
       VVec elemT len ->
         case len of
           VAdd1 k ->
             return (SThe elemT (CVecHead es'))
           other ->
             do len' <- readBack (NThe VNat len)
                failure [ MText (T.pack "Expected a Vec with non-zero length, got a Vec with")
                        , MVal (C len')
                        , MText (T.pack "length.")]
       other ->
         do t <- readBackType other
            failure [MText (T.pack "Expected a Vec, got a"), MVal (C t)]
synth' (VecTail es) =
  do SThe esT es' <- synth es
     case esT of
       VVec elemT len ->
         case len of
           VAdd1 k ->
             return (SThe (VVec elemT k) (CVecTail es'))
           other ->
             do len' <- readBack (NThe VNat len)
                failure [ MText (T.pack "Expected a Vec with non-zero length, got a Vec with")
                        , MVal (C len')
                        , MText (T.pack "length.")]
       other ->
         do t <- readBackType other
            failure [MText (T.pack "Expected a Vec, got a"), MVal (C t)]
synth' (IndVec len es mot base step) =
  do len' <- check VNat len
     lenv <- eval len'
     SThe esT es' <- synth es
     case esT of
       VVec elem len'' ->
         do same VNat lenv len''
            motT <- evalInEnv (None :> (sym "E", elem))
                      (CPi (sym "k") CNat
                        (CPi (sym "es") (CVec (CVar (sym "E")) (CVar (sym "k")))
                          CU))
            mot' <- check motT mot
            motv <- eval mot'
            baseT <- doApplyMany motv [VZero, VVecNil]
            base' <- check baseT base
            stepT <- evalInEnv (None :> (sym "E", elem) :> (sym "mot", motv))
                       (CPi (sym "k") CNat
                         (CPi (sym "e") (CVar (sym "E"))
                           (CPi (sym "es") (CVec (CVar (sym "E")) (CVar (sym "k")))
                             (CPi (sym "so-far") (CApp (CApp (CVar (sym "mot"))
                                                             (CVar (sym "k")))
                                                       (CVar (sym "es")))
                               (CApp (CApp (CVar (sym "mot"))
                                           (CAdd1 (CVar (sym "k"))))
                                      (CVecCons (CVar (sym "e"))
                                                (CVar (sym "es"))))))))
            step' <- check stepT step
            lenv <- eval len'
            esv <- eval es'
            ty <- doApplyMany motv [lenv, esv]
            return (SThe ty (CIndVec len' es' mot' base' step'))
       other ->
         do t <- readBackType other
            failure [MText (T.pack "Expected a Vec, got a"), MVal (C t)]
synth' (Either l r) =
  do l' <- check VU l
     r' <- check VU r
     return (SThe VU (CEither l' r'))
synth' (IndEither tgt mot l r) =
  do SThe tgtT tgt' <- synth tgt
     case tgtT of
       VEither lt rt ->
         do motT <- evalInEnv (None :> (sym "L", lt) :> (sym "R", rt))
                      (CPi (sym "x") (CEither (CVar (sym "L")) (CVar (sym "R")))
                        CU)
            mot' <- check motT mot
            motv <- eval mot'
            lmt <- evalInEnv (None :> (sym "L", lt) :> (sym "mot", motv))
                     (CPi (sym "l") (CVar (sym "L"))
                       (CApp (CVar (sym "mot")) (CLeft (CVar (sym "l")))))
            l' <- check lmt l
            rmt <- evalInEnv (None :> (sym "R", rt) :> (sym "mot", motv))
                     (CPi (sym "r") (CVar (sym "R"))
                       (CApp (CVar (sym "mot")) (CRight (CVar (sym "r")))))
            r' <- check rmt r
            tgtv <- eval tgt'
            ty <- evalInEnv (None :> (sym "tgt", tgtv) :> (sym "mot", motv))
                    (CApp (CVar (sym "mot")) (CVar (sym "tgt")))
            return (SThe ty (CIndEither tgt' mot' l' r'))

       other ->
         do t <- readBackType other
            failure [ MText (T.pack "Not Either:")
                    , MVal (C t)
                    ]
synth' Absurd = return (SThe VU CAbsurd)
synth' (IndAbsurd tgt mot) =
  do tgt' <- check VAbsurd tgt
     mot' <- check VU mot
     motv <- eval mot'
     return (SThe motv (CIndAbsurd tgt' mot'))
synth' other =
  do loc <- currentLoc
     failure [ MText (T.pack "Can't synth")
             , MVal (E (Expr loc other))
             ]

check :: Value -> Expr -> Elab Core
check t e =
  do res <- inExpr e (check' t)
     tc <- readBackType t
     inExpr e (const (logInfo (ExprHasType tc)))
     return res

check' t (Lambda ((loc, x) :| xs) body) =
  case t of
    VPi y dom ran ->
      do z <- fresh x
         withCtxExtension z (Just loc) dom $
           do bodyT <- instantiate ran y (VNeu dom (NVar z))
              case xs of
                [] ->
                  do body' <- rename x z $
                              check bodyT body
                     return (CLambda z body')
                (y : ys) ->
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
check' t ListNil =
  case t of
    VList elem -> return CListNil
    other ->
      do t' <- readBackType other
         failure [MText (T.pack "Not a Vec type"), MVal (C t')]
check' t (VecCons e es) =
  case t of
    VVec elem len ->
      case len of
        VAdd1 k ->
          CVecCons <$> check elem e <*> check (VVec elem k) es
        otherLen ->
          do len' <- readBack (NThe VNat otherLen)
             failure [ MText (T.pack "Expected a non-zero length, got a Vec type with")
                     , MVal (C len')
                     , MText (T.pack "length.")]

    other ->
      do t' <- readBackType other
         failure [MText (T.pack "Not a Vec type"), MVal (C t')]
check' t VecNil =
  case t of
    VVec elem len ->
      case len of
        VZero ->
          return CVecNil
        otherLen ->
          do len' <- readBack (NThe VNat otherLen)
             failure [ MText (T.pack "Expected zero length in Vec, got a")
                     , MVal (C len')
                     , MText (T.pack "length.")]

    other ->
      do t' <- readBackType other
         failure [MText (T.pack "Not a Vec type"), MVal (C t')]
check' t (EitherLeft l) =
  case t of
    VEither lt _ ->
      CLeft <$> check lt l
    other ->
      do t' <- readBackType other
         failure [MText (T.pack "Not Either"), MVal (C t')]
check' t (EitherRight r) =
  case t of
    VEither _ rt ->
      CRight <$> check rt r
    other ->
      do t' <- readBackType other
         failure [MText (T.pack "Not Either"), MVal (C t')]

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

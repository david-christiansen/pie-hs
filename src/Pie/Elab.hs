{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module Pie.Elab where

import Data.Char (isLetter, isMark)
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

failure :: [MessagePart Core] -> Elab a
failure msg = Elab (\ ctx loc _ -> ([], Left (ElabErr (Located loc msg))))

getCtx :: Elab (Ctx Value)
getCtx = Elab (\ ctx _ _ -> ([], pure ctx))

currentLoc :: Elab Loc
currentLoc = Elab (\_ loc _ -> ([], pure loc))

applyRenaming :: Symbol -> Elab Symbol
applyRenaming x =
  Elab (\ _ loc ren ->
          case lookup x ren of
            Nothing -> ([], Left (ElabErr (Located loc [MText (T.pack ("Unknown variable")), MVal (CVar x), MText (T.pack ("in " ++ show ren))])))
            Just y -> ([], pure y))

rename :: Symbol -> Symbol -> Elab a -> Elab a
rename from to (Elab act) =
  Elab (\ ctx loc ren -> act ctx loc ((from, to) : ren))

withModifiedCtx :: (Ctx Value -> Ctx Value) -> Elab a -> Elab a
withModifiedCtx f (Elab act) =
  Elab (\ctx loc ren -> act (f ctx) loc ren)

withCtxExtension :: Symbol -> Maybe Loc -> Value -> Elab a -> Elab a
withCtxExtension x loc t = withModifiedCtx (:> (x, HasType loc t))

withCtx :: Ctx Value -> Elab a -> Elab a
withCtx ctx = withModifiedCtx (const ctx)

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

-- TODO Consider splitting the nested formation rules for →, Π, Σ at top-level
-- for consistency with inference rule presentation
isType' :: (Expr' Loc) -> Elab Core
-- AtomF on p. 371
isType' Atom = pure CAtom
-- ΣF on p. 371
isType' (Sigma ((loc, x, a) :| as) d) =
  do a' <- isType a
     aVal <- eval a'
     x' <- fresh x
     d' <- withCtxExtension x (Just loc) aVal $
           rename x x' $
             case as of
               -- ΣF-1
               [] ->
                 isType d
               -- ΣF-2
               (nextA : ds) ->
                 isType' (Sigma (nextA :| ds) d)
     return (CSigma x' a' d')
-- ΣF-Pair on p. 372
isType' (Pair a d) =
  do x <- fresh (Symbol (T.pack "x"))
     a' <- isType a
     aVal <- eval a'
     d' <- withCtxExtension x Nothing aVal $ isType d
     return (CSigma x a' d')
-- FunF on p. 373
isType' (Pi ((loc, x, arg) :| args) r) =
  do arg' <- isType arg
     argVal <- eval arg'
     x' <- fresh x
     r' <- withCtxExtension x' (Just loc) argVal $
           rename x x' $
           case args of
             -- FunF-1
             [] ->
               isType r
             -- FunF-2
             (nextArg : ds) ->
               isType' (Pi (nextArg :| ds) r)
     return (CPi x' arg' r')
-- FunF→ on p. 373
isType' (Arrow arg (t:|ts)) =
  do x <- fresh (Symbol (T.pack "x"))
     arg' <- isType arg
     argVal <- eval arg'
     r' <- withCtxExtension x Nothing argVal $
           case ts of
             -- FunF→1
             [] ->
               isType t
             -- FunF→2
             (ty : tys) ->
               isType' (Arrow t (ty :| tys))
     return (CPi x arg' r')
-- NatF on p. 374
isType' Nat = pure CNat
-- ListF on p. 378
isType' (List e) = CList <$> isType e
-- VecF on p. 381
isType' (Vec e len) = CVec <$> isType e <*> check VNat len
-- EqF on p. 383
isType' (Eq x from to) =
  do x' <- isType x
     xVal <- eval x'
     CEq x' <$> check xVal from <*> check xVal to
-- EitherF on p. 386
isType' (Either p s) = CEither <$> isType p <*> isType s
-- TrivF on p. 387
isType' Trivial = return CTrivial
-- AbsF on p. 388
isType' Absurd = return CAbsurd
-- UF on p. 389
isType' U = pure CU
-- El on p. 389
isType' other = check' VU other


data SynthResult = SThe { theType :: Value, theExpr :: Core }
  deriving Show

toplevel e =
  do (SThe tv e') <- synth e
     t <- readBackType tv
     val <- eval e'
     eN <- readBack (NThe tv val)
     return (CThe t eN)

-- Implements Γ ⊢ x lookup ⤳ X
findVar x None =
  do loc <- currentLoc
     failure [MText (T.pack "Unknown variable"), MVal (CVar x)]
findVar x (ctx' :> (y, info))
  -- LookupStop on p. 370
  | x == y =
     pure (SThe (entryType info) (CVar x))
  -- LookupPop on p. 370
  | otherwise = findVar x ctx'



synth :: Expr -> Elab SynthResult
synth e =
  do res@(SThe tv _) <- inExpr e synth'
     t <- readBackType tv
     inExpr e (const (logInfo (ExprHasType t)))
     return res

-- The on p. 367
synth' (The ty e) =
  do ty' <- isType ty
     tv <- eval ty'
     e' <- check tv e
     return (SThe tv (CThe ty' e'))
-- Hypothesis on p. 370
synth' (Var x) =
  do ctx <- getCtx
     x' <- applyRenaming x
     findVar x' ctx
-- AtomI on p. 371
synth' (Tick sym)
  | T.all (\ch -> isLetter ch || isMark ch || ch == '-') (symbolName sym) &&
    T.length (symbolName sym) > 0 =
    pure (SThe VAtom (CTick sym))
  | otherwise =
    failure [MText (T.pack "Atoms may contain only letters and hyphens")]
-- ΣE-1 on p. 372
synth' (Car pr) =
  do SThe ty pr' <- synth pr
     case ty of
       VSigma x aT dT ->
         return (SThe aT (CCar pr'))
       other ->
         do ty <- readBackType other
            failure [MText (T.pack "Not a Σ: "), MVal ty]
-- ΣE-2 on p. 372
synth' (Cdr pr) =
  do SThe ty pr' <- synth pr
     case ty of
       VSigma x aT dT ->
         do a <- eval pr' >>= doCar
            dV <- instantiate dT x a
            return (SThe dV (CCdr pr'))
       other ->
         do ty <- readBackType other
            failure [MText (T.pack "Not a Σ: "), MVal ty]
-- FunE-1 and FunE-2 on p. 374
synth' (App f (arg1 :| args)) =
  do (SThe fT f') <- synth f
     checkArgs f' fT (arg1 :| args)

  where
    checkArgs fun (VPi x dom ran) (arg1 :| args) =
      do arg1' <- check dom arg1
         arg1v <- eval arg1'
         exprTy <- instantiate ran x arg1v
         case args of
           -- Fun-E1
           [] -> return (SThe exprTy (CApp fun arg1'))
           -- Fun-E2
           (r:rs) -> checkArgs (CApp fun arg1') exprTy (r :| rs)
    checkArgs _ other _ =
      do t <- readBackType other
         failure [MText (T.pack "Not a Π type: "), MVal t]
-- NatI-1 on p. 374
synth' Zero = pure (SThe VNat CZero)
-- NatI-2 on p. 375
synth' (Add1 n) =
  do n' <- check VNat n
     return (SThe VNat (CAdd1 n'))
-- NatI-3 and NatI-4 on p. 375
synth' (NatLit n)
  -- NatI-3
  | n <= 0 = synth' Zero
  -- NatI-4
  | otherwise =
    do loc <- currentLoc
       synth' (Add1 (Expr loc (NatLit (n - 1))))
-- NatE-1 on p. 375
synth' (WhichNat tgt base step) =
  do tgt' <- check VNat tgt
     SThe bt base' <- synth base
     stepT <- evalInEnv (None :> (sym "base-type", bt))
                (CPi (sym "x") CNat
                  (CVar (sym "base-type")))
     step' <- check stepT step
     bt' <- readBackType bt
     return (SThe bt (CWhichNat tgt' bt' base' step'))
-- NatE-2 on p. 376
synth' (IterNat tgt base step) =
  do tgt' <- check VNat tgt
     SThe bt base' <- synth base
     stepT <- evalInEnv
                (None :> (sym "base-type", bt))
                (CPi (sym "x") (CVar (sym "base-type")) (CVar (sym "base-type")))
     step' <- check stepT step
     bt' <- readBackType bt
     return (SThe bt (CIterNat tgt' bt' base' step'))
-- NatE-3 on p. 376
synth' (RecNat tgt base step) =
  do tgt' <- check VNat tgt
     SThe bt base' <- synth base
     stepT <- evalInEnv
                (None :> (sym "base-type", bt))
                (CPi (sym "n") CNat
                  (CPi (sym "x") (CVar (sym "base-type"))
                    (CVar (sym "base-type"))))
     step' <- check stepT step
     bt' <- readBackType bt
     return (SThe bt (CRecNat tgt' bt' base' step'))
-- NatE-4 on p. 377
synth' (IndNat tgt mot base step) =
  do tgt' <- check VNat tgt
     mot' <- check (VPi (sym "x") VNat (Closure None CU)) mot
     motV <- eval mot'
     baseT <- doApply motV VZero
     base' <- check baseT base
     stepT <- evalInEnv (None :> (sym "mot", motV))
                (CPi (sym "k") CNat
                  (CPi (sym "almost") (CApp (CVar (sym "mot")) (CVar (sym "k")))
                    (CApp (CVar (sym "mot")) (CAdd1 (CVar (sym "k"))))))
     step' <- check stepT step
     tgtV <- eval tgt'
     ty <- doApply motV tgtV
     return (SThe ty (CIndNat tgt' mot' base' step'))
-- ListI-2 on p. 378
synth' (ListCons e es) =
  do SThe et e' <- synth e
     es' <- check (VList et) es
     return (SThe (VList et) (CListCons e' es'))
-- ListE-1 on p. 379
-- The mandatory "the" around the base in the book is represented by
-- the extra argument to CRecList in this implementation.
synth' (RecList tgt base step) =
  do SThe lstT tgt' <- synth tgt
     case lstT of
       VList et ->
         do (SThe bt base') <- synth base
            stepT <- evalInEnv (None :> (sym "E", et) :> (sym "base-type", bt))
                       (CPi (sym "e") (CVar (sym "E"))
                         (CPi (sym "es") (CList (CVar (sym "E")))
                           (CPi (sym "almost") (CVar (sym "base-type"))
                             (CVar (sym "base-type")))))
            step' <- check stepT step
            bt' <- readBackType bt
            return (SThe bt (CRecList tgt' bt' base' step'))
       other ->
         do t <- readBackType other
            failure [MText (T.pack "Not a List type: "), MVal t]
-- ListE-2 on p. 380
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
            failure [MText (T.pack "Not a List type: "), MVal t]
-- VecE-1 on p. 381
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
                        , MVal len'
                        , MText (T.pack "length.")]
       other ->
         do t <- readBackType other
            failure [MText (T.pack "Expected a Vec, got a"), MVal t]
-- VecE-2 on p. 381
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
                        , MVal len'
                        , MText (T.pack "length.")]
       other ->
         do t <- readBackType other
            failure [MText (T.pack "Expected a Vec, got a"), MVal t]
-- VecE-3 on p. 382
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
            failure [MText (T.pack "Expected a Vec, got a"), MVal t]
-- EqE-1 on p. 383
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
            failure [MText (T.pack "Not an = type: "), MVal t]
-- EqE-2 on p. 384
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
                failure [MText (T.pack "Not an -> type: "), MVal t]
       other ->
         do t <- readBackType other
            failure [MText (T.pack "Not an = type: "), MVal t]
-- EqE-3 on p. 384
synth' (Symm tgt) =
  do SThe tgtT tgt' <- synth tgt
     case tgtT of
       VEq a from to ->
         return (SThe (VEq a to from) (CSymm tgt'))
       other ->
         do t <- readBackType other
            failure [MText (T.pack "Not an = type: "), MVal t]
-- EqE-4 on p. 385
synth' (Trans p1 p2) =
  do SThe t1 p1' <- synth p1
     SThe t2 p2' <- synth p2
     case t1 of
       VEq a from mid ->
         case t2 of
           VEq b mid' to ->
             do sameType a b
                same a mid mid'
                return (SThe (VEq a from to) (CTrans p1' p2'))
           other2 ->
             do notEq <- readBackType other2
                failure [ MText (T.pack "Not an = type: "), MVal notEq]
       other1 ->
         do notEq <- readBackType other1
            failure [ MText (T.pack "Not an = type: "), MVal notEq]
-- EqE-5 on p. 385
synth' (IndEq tgt mot base) =
  do SThe tgtT tgt' <- synth tgt
     case tgtT of
       VEq a from to ->
         do let env = None :> (sym "a", a) :> (sym "from", from)
                motTy = VPi (sym "x") a
                          (Closure env
                            (CPi (sym "eq") (CEq (CVar (sym "a")) (CVar (sym "from")) (CVar (sym "x")))
                              CU))
            mot' <- check motTy mot
            motv <- eval mot'
            baseT <- doApplyMany motv [from, (VSame from)]
            base' <- check baseT base
            tgtv <- eval tgt'
            ty <- doApplyMany motv [to, tgtv]
            return (SThe ty (CIndEq tgt' mot' base'))
       other ->
         do notEq <- readBackType other
            failure [ MText (T.pack "Not an = type: "), MVal notEq]
-- EitherE on p. 386
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
                    , MVal t
                    ]
-- TrivI on p. 387
synth' Sole = return (SThe VTrivial CSole)
-- AbsE on p. 388
synth' (IndAbsurd tgt mot) =
  do tgt' <- check VAbsurd tgt
     mot' <- check VU mot
     motv <- eval mot'
     return (SThe motv (CIndAbsurd tgt' mot'))
-- UI-1 on p. 389
synth' Atom = pure (SThe VU CAtom)
-- UI-2 and UI-3 on p. 389
synth' (Sigma ((loc, x, a) :| as) d) =
  do a' <- check VU a
     aVal <- eval a'
     x' <- fresh x
     d' <- withCtxExtension x (Just loc) aVal $
             rename x x' $
             case as of
               -- UI-2
               [] ->
                 check VU d
               -- UI-3
               ((loc, y, d) : ds) ->
                 check' VU (Pi ((loc, y, d) :| ds) d)
     return (SThe VU (CSigma x a' d'))
-- UI-4 on p. 389
synth' (Pair a d) =
  do a' <- check VU a
     aVal <- eval a'
     x <- fresh (sym "a")
     d' <- withCtxExtension x Nothing aVal $ check VU d
     return (SThe VU (CSigma x a' d'))
-- UI-5 and UI-6 on pp. 389, 390
synth' (Pi ((loc, x, dom) :| doms) ran) =
  do dom' <- check VU dom
     domVal <- eval dom'
     x' <- fresh x
     ran' <- rename x x' $ withCtxExtension x' (Just loc) domVal $
             case doms of
               -- UI-5
               [] ->
                 check VU ran
               -- UI-6
               (y : ds) ->
                 check' VU (Pi (y :| ds) ran)
     return (SThe VU (CPi x' dom' ran'))
-- UI-7 and UI-8 on p. 390
synth' (Arrow dom (t:|ts)) =
  do x <- fresh (Symbol (T.pack "x"))
     dom' <- check VU  dom
     domVal <- eval dom'
     ran' <- withCtxExtension x Nothing domVal $
             case ts of
               -- UI-7
               [] ->
                 check VU t
               -- UI-8
               (ty : tys) ->
                 check' VU (Arrow t (ty :| tys))
     return (SThe VU (CPi x dom' ran'))
-- UI-9 on p. 390
synth' Nat = pure (SThe VU CNat)
-- UI-10 on p. 390
synth' (List elem) =
  do elem' <- check VU elem
     return (SThe VU (CList elem'))
-- UI-11 on p. 390
synth' (Vec elem len) =
  SThe VU <$> (CVec <$> check VU elem <*> check VNat len)
-- UI-12 on p. 390
synth' (Eq ty from to) =
  do ty' <- check VU ty
     tv <- eval ty'
     from' <- check tv from
     to' <- check tv to
     return (SThe VU (CEq ty' from' to'))
-- UI-13 on p. 391
synth' (Either l r) =
  do l' <- check VU l
     r' <- check VU r
     return (SThe VU (CEither l' r'))
-- UI-14 on p. 391
synth' Trivial = return (SThe VU CTrivial)
-- UI-15 on p. 391
synth' Absurd = return (SThe VU CAbsurd)
synth' other =
  do loc <- currentLoc
     failure [ MText (T.pack "Can't synth")
             , MText (T.pack (show other)) -- TODO better representation
             ]

check :: Value -> Expr -> Elab Core
check t e =
  do res <- inExpr e (check' t)
     tc <- readBackType t
     inExpr e (const (logInfo (ExprHasType tc)))
     return res

-- ΣI on p. 372
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
         failure [MText (T.pack "Not a pair type"), MVal t']
-- FunI-1 and FunI-2 on p. 373
check' t (Lambda ((loc, x) :| xs) body) =
  case t of
    VPi y dom ran ->
      do z <- fresh x
         withCtxExtension z (Just loc) dom $
           do bodyT <- instantiate ran y (VNeu dom (NVar z))
              case xs of
                -- FunI-1
                [] ->
                  do body' <- rename x z $
                              check bodyT body
                     return (CLambda z body')
                -- FunI-2
                (y : ys) ->
                  do body' <- rename x z $
                              check' bodyT (Lambda (y :| ys) body)
                     return (CLambda z body')
    other ->
      do t' <- readBackType other
         failure [MText (T.pack "Not a function type"), MVal t']
-- ListI-1 on p. 378
check' t ListNil =
  case t of
    VList elem -> return CListNil
    other ->
      do t' <- readBackType other
         failure [MText (T.pack "Not a Vec type"), MVal t']
-- VecI-1 on p. 381
check' t VecNil =
  case t of
    VVec elem len ->
      case len of
        VZero ->
          return CVecNil
        otherLen ->
          do len' <- readBack (NThe VNat otherLen)
             failure [ MText (T.pack "Expected zero length in Vec, got a")
                     , MVal len'
                     , MText (T.pack "length.")]

    other ->
      do t' <- readBackType other
         failure [MText (T.pack "Not a Vec type"), MVal t']
-- VecI-2 on p. 381
check' t (VecCons e es) =
  case t of
    VVec elem len ->
      case len of
        VAdd1 k ->
          CVecCons <$> check elem e <*> check (VVec elem k) es
        otherLen ->
          do len' <- readBack (NThe VNat otherLen)
             failure [ MText (T.pack "Expected a non-zero length, got a Vec type with")
                     , MVal len'
                     , MText (T.pack "length.")]

    other ->
      do t' <- readBackType other
         failure [MText (T.pack "Not a Vec type"), MVal t']
-- EqI on p. 383
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
         failure [MText (T.pack "Not an equality type"), MVal t']
-- EitherI-1 on p. 386
check' t (EitherLeft l) =
  case t of
    VEither lt _ ->
      CLeft <$> check lt l
    other ->
      do t' <- readBackType other
         failure [MText (T.pack "Not Either"), MVal t']
-- EitherI-2 on p. 386
check' t (EitherRight r) =
  case t of
    VEither _ rt ->
      CRight <$> check rt r
    other ->
      do t' <- readBackType other
         failure [MText (T.pack "Not Either"), MVal t']
check' t TODO =
  do t' <- readBackType t
     loc <- currentLoc
     ctx <- getTODOctx
     logInfo (FoundTODO ctx t')
     return (CTODO loc t')
  where
    getTODOctx =
      getCtx >>= processCtx

    -- Note: this relies on the invariant that there are no local
    -- binding forms that extend the context with definitions. If
    -- "let" is added to Pie, this needs revisiting.
    processCtx (ctx :> (x, HasType loc ty)) =
      (:>) <$> processCtx ctx <*> fmap (\t -> (x, loc, t)) (readBackType ty)
    processCtx _ = return None

-- Switch, p. 367
-- This rule must come last because it uses a catch-all pattern.
check' t other =
  do SThe t' other' <- synth' other
     sameType t t'
     return other'

-- This checks the form of judgment Γ ⊢ e₁ ≡ e₂ : t
same :: Value -> Value -> Value -> Elab ()
same ty v1 v2 =
  do c1 <- readBack (NThe ty v1)
     c2 <- readBack (NThe ty v2)
     case alphaEquiv c1 c2 of
       Left (l, r) ->
         do t <- readBackType ty
            failure $ [ MVal c1
                      , MText (T.pack "is not the same")
                      , MVal t
                      , MText (T.pack "as")
                      , MVal c2
                      ] ++
                      if l /= c1
                        then [ MText (T.pack "because")
                             , MVal l
                             , MText (T.pack "doesn't match")
                             , MVal r
                             ]
                        else []
       Right _ -> pure ()

-- This checks the form of judgment Γ ⊢ t₁ ≡ t₂ type
sameType :: Value -> Value -> Elab ()
sameType v1 v2 =
  do c1 <- readBackType v1
     c2 <- readBackType v2
     case alphaEquiv c1 c2 of
       Left (l, r) ->
         failure $ [ MVal c1
                 , MText (T.pack "is not the same type as")
                 , MVal c2
                 ] ++
                 if l /= c1
                   then [ MText (T.pack "because")
                        , MVal l
                        , MText (T.pack "doesn't match")
                        , MVal r
                        ]
                   else []
       Right _ -> pure ()

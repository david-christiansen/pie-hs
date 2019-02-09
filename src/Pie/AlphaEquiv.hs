module Pie.AlphaEquiv (alphaEquiv) where

import Pie.Types

alphaEquiv e1 e2 = runAlpha (equiv e1 e2) [] [] 0

newtype Alpha a =
  Alpha { runAlpha ::
            [(Symbol, Integer)] -> [(Symbol, Integer)] ->
            Integer ->
            Either (Core, Core) a
        }

instance Functor Alpha where
  fmap f (Alpha act) = Alpha (\ l r i -> fmap f (act l r i))

instance Applicative Alpha where
  pure x = Alpha (\ _ _ _ -> Right x)
  Alpha fun <*> Alpha arg =
    Alpha (\ l r i -> fun l r i <*> arg l r i)



withEquiv :: Symbol -> Symbol -> Alpha a -> Alpha a
withEquiv x y (Alpha act) =
  Alpha (\ l r i -> act ((x, i) : l) ((y, i) : r) (i + 1))

notEquiv :: Core -> Core -> Alpha a
notEquiv e1 e2 = Alpha (\ l r i -> Left (e1, e2))

equivVars :: Symbol -> Symbol -> Alpha ()
equivVars x y =
  Alpha (\l r _ ->
           case (lookup x l, lookup y r) of
             (Nothing, Nothing)
               | x == y    -> pure ()
               | otherwise -> Left (CVar x, CVar y)
             (Just i, Just j)
               | i == j    -> pure ()
               | otherwise -> Left (CVar x, CVar y)
             _ -> Left (CVar x, CVar y))

equiv :: Core -> Core -> Alpha ()
equiv e1 e2 =
  case (e1, e2) of
    (CTick x, CTick y) ->
      require (x == y)
    (CAtom, CAtom) ->
      yes
    (CZero, CZero) ->
      yes
    (CAdd1 j, CAdd1 k) ->
      equiv j k
    (CIndNat tgt1 mot1 base1 step1, CIndNat tgt2 mot2 base2 step2) ->
      equiv tgt1 tgt2 *>
      equiv mot1 mot2 *>
      equiv base1 base2 *>
      equiv step1 step2
    (CNat, CNat) ->
      yes
    (CVar x, CVar y) ->
      equivVars x y
    (CPi x dom1 ran1, CPi y dom2 ran2) ->
      equiv dom1 dom2 *>
      withEquiv x y (equiv ran1 ran2)
    (CLambda x body1, CLambda y body2) ->
      withEquiv x y (equiv body1 body2)
    (CApp rator1 rand1, CApp rator2 rand2) ->
      equiv rator1 rator2 *>
      equiv rand1 rand2
    (CSigma x a1 d1, CSigma y a2 d2) ->
      equiv a1 a2 *>
      withEquiv x y (equiv d1 d2)
    (CCons a1 d1, CCons a2 d2) ->
      equiv a1 a2 *> equiv d1 d2
    (CCar p1, CCar p2) -> equiv p1 p2
    (CCdr p1, CCdr p2) -> equiv p1 p2
    (CTrivial, CTrivial) -> yes
    (CSole, CSole) -> yes
    (CU, CU) ->
      yes
    (CEq a f1 t1, CEq b f2 t2) ->
      equiv a b *> equiv f1 f2 *> equiv t1 t2
    (CSame e1, CSame e2) ->
      equiv e1 e2
    (CReplace tgt1 mot1 base1, CReplace tgt2 mot2 base2) ->
      equiv tgt1 tgt2 *> equiv mot1 mot2 *> equiv base1 base2
    (CTrans a1 b1, CTrans a2 b2) ->
      equiv a1 a2 *> equiv b1 b2
    (CCong a1 b1 c1, CCong a2 b2 c2) ->
      equiv a1 a2 *> equiv b1 b2 *> equiv c1 c2
    (CSymm p1, CSymm p2) ->
      equiv p1 p2
    (CIndEq tgt1 mot1 base1, CIndEq tgt2 mot2 base2) ->
      equiv tgt1 tgt2 *> equiv mot1 mot2 *> equiv base1 base2
    (CThe t1 e1, CThe t2 e2) ->
      equiv t1 t2 *> equiv e1 e2
    _ ->
      no

  where
    yes = pure ()
    no = notEquiv e1 e2
    require b = if b then yes else no

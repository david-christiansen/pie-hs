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
    (CU, CU) ->
      yes
    _ ->
      no

  where
    yes = pure ()
    no = notEquiv e1 e2
    require b = if b then yes else no

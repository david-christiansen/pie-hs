module Main where

import Test.Tasty
import Test.Tasty.HUnit

import Pie.Types
import Pie.AlphaEquiv
import qualified Pie.Elab as E
import qualified Pie.Normalize as N
import qualified Pie.Parse as P


main = defaultMain tests

tests = testGroup "Pie tests" [normTests]


normTests =
  testGroup "Normalization"
    [ testCase (input ++ " has normal form " ++ normal) (hasNorm input normal)
    | (input, normal) <-
        -- Base types
        [ ("(the Trivial sole)", "sole")
        , ("4", "(add1 (add1 (add1 (add1 zero))))")
        -- η rules
        , ( "(the (Pi ((x (Pair Trivial Trivial))) (Pair Trivial Trivial)) (lambda (x) x))"
          , "(the (Pi ((y (Pair Trivial Trivial))) (Pair Trivial Trivial)) (lambda (z) (cons sole sole)))"
          )
        , ( "(the (-> (-> Trivial Trivial) (-> Trivial Trivial)) (lambda (x) x))"
          , "(the (-> (-> Trivial Trivial) (-> Trivial Trivial)) (lambda (f) (lambda (x) sole)))"
          )
        , ( "(the (-> (-> Nat Nat) (-> Nat Nat)) (lambda (x) x))"
          , "(the (-> (-> Nat Nat) (-> Nat Nat)) (lambda (f) (lambda (x) (f x))))"
          )
        ]
    ]

mustSucceed ::
  Show e =>
  Either e a ->
  IO a
mustSucceed (Left e) = assertFailure (show e)
mustSucceed (Right x) = return x

mustParse :: P.Parser a -> String -> IO a
mustParse p e = mustSucceed (P.testParser p e)

mustParseExpr :: String -> IO Expr
mustParseExpr = mustParse P.expr

mustElab :: E.Elab a -> IO a
mustElab act = mustSucceed (E.runElab act None (Loc "<test suite>" (Pos 1 1) (Pos 1 1)) [])


mustBeAlphaEquiv :: Core -> Core -> IO ()
mustBeAlphaEquiv c1 c2 = mustSucceed (alphaEquiv c1 c2)

norm :: N.Norm a -> a
norm act = N.runNormalize act [] None

hasNorm ::
  String {- ^ The input expression -} ->
  String {- ^ The supposed normal form -} ->
  Assertion
hasNorm input normal =
  do normStx <- mustParseExpr normal
     inputStx <- mustParseExpr input
     (E.SThe ty1 normCore) <- mustElab (E.synth normStx)
     (E.SThe ty2 inputCore) <- mustElab (E.synth inputStx)
     mustElab (E.sameType ty1 ty2)
     let newNorm = norm $
                   do v <- N.eval inputCore
                      N.readBack (NThe ty1 v)
     mustBeAlphaEquiv normCore newNorm

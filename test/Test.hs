module Main where

import Data.List.NonEmpty(NonEmpty(..))
import Data.Text (Text)
import qualified Data.Text as T
import Test.Tasty
import Test.Tasty.HUnit

import Pie.Fresh
import Pie.Types
import Pie.AlphaEquiv
import qualified Pie.Elab as E
import qualified Pie.Normalize as N
import qualified Pie.Parse as P


main = defaultMain tests

tests = testGroup "Pie tests" [freshNames, alpha, normTests, testTick, parsingSourceLocs]


normTests =
  testGroup "Normalization"
    [ testCase (input ++ " has normal form " ++ normal) (hasNorm input normal)
    | (input, normal) <-
        -- Base types
        [ ("(the Trivial sole)", "sole")
        , ("4", "(add1 (add1 (add1 (add1 zero))))")
        -- Irrelevance for Trivial
        , ( "(the (Pi ((x Trivial) (y Trivial)) (= Trivial x y)) (lambda (x y) (same x)))"
          , "(the (Pi ((x Trivial) (y Trivial)) (= Trivial x y)) (lambda (x y) (same sole)))"
          )
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

freshNames =
  testGroup "Freshness"
   [ testCase (show used ++ " : " ++ T.unpack (symbolName x) ++ " ⇒ " ++ T.unpack (symbolName x'))
       (x' @=? freshen used x)
   | (used, x, x') <- [ ([sym "x"], sym "x", sym "x₁")
                      , ([sym "x", sym "x₁", sym "x₂"], sym "x", sym "x₃")
                      , ([sym "x", sym "x1", sym "x2"], sym "y", sym "y")
                      , ([sym "r2d", sym "r2d₀", sym "r2d₁"], sym "r2d", sym "r2d₂")
                      , ([], sym "A", sym "A")
                      , ([sym "x₁"], sym "x₁", sym "x₂")
                      , ([], sym "x₁", sym "x₁")
                      , ([], sym "₉₉", sym "₉₉")
                      , ([sym "₉₉"], sym "₉₉", sym "x₉₉")
                      , ([sym "₉₉", sym "x₉₉"], sym "₉₉", sym "x₁₀₀")
                      ]
   ]

alpha = testGroup "α-equivalence" $
  let x = sym "x"
      y = sym "y"
      z = sym "z"
      f = sym "f"
      g = sym "g"
      loc1 = Loc "hello.pie" (Pos 1 1) (Pos 1 5)
      loc2 = Loc "hello.pie" (Pos 3 4) (Pos 3 8)
  in [ testAlpha left right res
     | (left, right, res) <-
       [ (CLambda x (CVar x), CLambda x (CVar x), True)
       , (CLambda x (CVar x), CLambda y (CVar y), True)
       , (CLambda x (CLambda y (CVar x)) , CLambda x (CLambda y (CVar x)), True)
       , (CLambda x (CLambda y (CVar x)) , CLambda y (CLambda z (CVar y)), True)
       , (CLambda x (CLambda y (CVar x)) , CLambda y (CLambda z (CVar z)), False)
       , (CLambda x (CLambda y (CVar x)) , CLambda y (CLambda x (CVar x)), False)
       , (CLambda x (CVar x), CLambda y (CVar x), False)
       , (CVar x, CVar x, True)
       , (CVar x, CVar y, False)
       , (CApp (CVar f) (CVar x), CApp (CVar f) (CVar x), True)
       , (CApp (CVar f) (CVar x), CApp (CVar g) (CVar x), False)
       , (CLambda f (CApp (CVar f) (CVar x)), CLambda g (CApp (CVar g) (CVar x)), True)
       , (CZero, CZero, True)
       , (CAdd1 CZero, CAdd1 CZero, True)
       , (CTick (sym "rugbrød"), CTick (sym "rugbrød"), True)
       , (CTick (sym "rugbrød"), CTick (sym "rundstykker"), False)
       , ( CSigma (sym "half") CNat
            (CEq CNat (CVar (sym "n")) (CApp (CVar (sym "double")) (CVar (sym "half"))))
         , CSigma (sym "blurgh") CNat
           (CEq CNat (CVar (sym "n")) (CApp (CVar (sym "double")) (CVar (sym "blurgh"))))
         , True
         )
       , ( CSigma (sym "half") CNat
            (CEq CNat (CVar (sym "n")) (CApp (CVar (sym "double")) (CVar (sym "half"))))
         , CSigma (sym "half") CNat
           (CEq CNat (CVar (sym "n")) (CApp (CVar (sym "twice")) (CVar (sym "half"))))
         , False
         )
       , (CThe CAbsurd (CVar x), CThe CAbsurd (CVar x), True)
       , (CThe CAbsurd (CVar x), CThe CAbsurd (CVar y), True)
       , (CThe CAbsurd (CVar x), CThe CAbsurd (CApp (CVar (sym "find-the-proof")) (CVar x)), True)
       , (CTODO loc1 CNat, CTODO loc1 CNat, True)
       , (CTODO loc1 CNat, CTODO loc2 CNat, False)
       , (CZero, CVar (sym "naught"), False)
       , ( CPi (sym "n") CNat
             (CEq CNat (CVar (sym "n")) (CVar (sym "n")))
         , CPi (sym "m") CNat
             (CEq CNat (CVar (sym "m")) (CVar (sym "m")))
         , True
         )
       , ( CPi (sym "n") CNat
             (CEq CNat (CVar (sym "n")) (CVar (sym "n")))
         , CPi (sym "m") CNat
             (CEq CNat (CVar (sym "n")) (CVar (sym "n")))
         , False
         )
       , ( CPi (sym "n") CNat
             (CEq CNat (CVar (sym "n")) (CVar (sym "n")))
         , CSigma (sym "m") CNat
             (CEq CNat (CVar (sym "m")) (CVar (sym "m")))
         , False
         )
       ]
     ]
  where
    testAlpha left right res =
      let correct x = x @=? res
      in testCase (show left ++ " α≡? " ++ show right) $
         correct $
         case alphaEquiv left right of
           Left _ -> False
           Right _ -> True

testTick = testGroup "Validity checking of atoms" $
  [testCase ("'" ++ str ++ " OK") (mustElab (E.synth' (Tick (Symbol (T.pack str)))) *> pure ())
  | str <- ["food", "food---", "œ", "rugbrød", "देवनागरी", "日本語", "atØm", "λ", "λάμβδα"]
  ] ++
  [testCase ("'" ++ str ++ " not OK") (mustNotElab (E.synth' (Tick (Symbol (T.pack str)))))
  | str <- ["at0m", "\128758"]
  ]


parsingSourceLocs = testGroup "Source locations from parser"
  [ testCase (show str) (parseTest str test)
  | (str, test) <- theTests
  ]
  where
    parseTest str expected =
      do res <- mustSucceed (P.testParser P.expr str)
         if res == expected
           then return ()
           else assertFailure str

    theTests =
      [ ( "x"
        , Expr (Loc "<test input>" (Pos 1 1) (Pos 1 2)) $
          Var (sym "x")
        )
      ,( "zero"
        , Expr (Loc "<test input>" (Pos 1 1) (Pos 1 5)) $
          Zero
        )
      , ( "(f x)"
        , Expr (Loc "<test input>" (Pos 1 1) (Pos 1 6)) $
          App (Expr (Loc "<test input>" (Pos 1 2) (Pos 1 3)) $ Var (sym "f"))
              (Expr (Loc "<test input>" (Pos 1 4) (Pos 1 5)) (Var (sym "x")) :| [])
          )
      , ( "(lambda (x y) (add1 x))"
        , Expr (Loc "<test input>" (Pos 1 1) (Pos 1 24)) $
          Lambda ((Loc "<test input>" (Pos 1 10) (Pos 1 11), sym "x") :|
                  [(Loc "<test input>" (Pos 1 12) (Pos 1 13), sym "y")]) $
          Expr (Loc "<test input>" (Pos 1 15) (Pos 1 23))
               (Add1 (Expr (Loc "<test input>" (Pos 1 21) (Pos 1 22)) $ Var (sym "x")))
          )
      ]


mustSucceed ::
  Show e =>
  Either e a ->
  IO a
mustSucceed (Left e) = assertFailure (show e)
mustSucceed (Right x) = return x

mustFail ::
  Show a =>
  Either e a ->
  IO ()
mustFail (Left e) = return ()
mustFail (Right x) =
  assertFailure ("Expected failure, but succeeded with " ++ show x)


mustParse :: P.Parser a -> String -> IO a
mustParse p e = mustSucceed (P.testParser p e)

mustParseExpr :: String -> IO Expr
mustParseExpr = mustParse P.expr

mustElab :: E.Elab a -> IO a
mustElab act =
  mustSucceed (snd (E.runElab act None (Loc "<test suite>" (Pos 1 1) (Pos 1 1)) []))


mustNotElab :: Show a => E.Elab a -> IO ()
mustNotElab act =
  mustFail (snd (E.runElab act None (Loc "<test suite>" (Pos 1 1) (Pos 1 1)) []))




mustBeAlphaEquiv :: Core -> Core -> IO ()
mustBeAlphaEquiv c1 c2 = mustSucceed (alphaEquiv c1 c2)

norm :: N.Norm a -> a
norm act = N.runNorm act [] None

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

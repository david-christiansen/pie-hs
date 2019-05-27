module Main where

import Data.List (intersperse)
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

tests =
  testGroup "Pie tests"
    [freshNames, alpha, normTests, testTick, parsingSourceLocs, errorTests]

errorTests =
  testGroup "Error messages"
    [ testCase tm (nope tm msg)
    | (tm, msg) <-
        [ ( "'f00d"
          , ElabErr (Located (Loc "<test input>" (Pos 1 1) (Pos 1 6))
                      [MText (T.pack "Atoms may contain only letters and hyphens")])
          )
        ]
    ]
  where
    nope :: String -> ElabErr -> Assertion
    nope tm msg =
      do e <- mustParseExpr tm
         mustNotElabWith (== msg) (E.synth e)

normTests =
  testGroup "Normalization/Sameness"
    [ testCase
        (abbrev input ++ " is the same as " ++ abbrev normal)
        (areSame input normal)
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
          -- Pi
        , ( "(the (-> (-> Nat Nat) Nat Nat) (lambda (f x) (f x)))"
          , "(the (-> (-> Nat Nat) Nat Nat) (lambda (f x) (f x)))"
          )

          -- which-Nat
        , ( "(which-Nat zero 't (lambda (x) 'nil))", "(the Atom 't)")
        , ( "(which-Nat 13 't (lambda (x) 'nil))", "(the Atom 'nil)")
        , ( "(the (-> Nat Atom) (lambda (n) (which-Nat n 't (lambda (x) 'nil))))"
          , "(the (-> Nat Atom) (lambda (n) (which-Nat n 't (lambda (x) 'nil))))"
          )
          -- iter-Nat
        , ( "(iter-Nat zero 3 (lambda (x) (add1 x)))"
          , "(the Nat 3)"
          )
        , ( "(iter-Nat 2 3 (lambda (x) (add1 x)))"
          , "(the Nat 5)"
          )
        , ( "(the (-> Nat Nat Nat) (lambda (j k) (iter-Nat j k (lambda (x) (add1 x)))))"
          , "(the (-> Nat Nat Nat) (lambda (j k) (iter-Nat j k (lambda (x) (add1 x)))))"
          )
          -- rec-Nat
        , ( "(rec-Nat zero (the (List Nat) nil) (lambda (n-1 almost) (:: n-1 almost)))"
          , "(the (List Nat) nil)"
          )
        , ( "(rec-Nat 3 (the (List Nat) nil) (lambda (n-1 almost) (:: n-1 almost)))"
          , "(the (List Nat) (:: 2 (:: 1 (:: 0 nil))))"
          )
        , ( "(the (-> Nat (List Nat)) (lambda (n) (rec-Nat n (the (List Nat) nil) (lambda (n-1 almost) (:: n-1 almost)))))"
          , "(the (-> Nat (List Nat)) (lambda (n) (rec-Nat n (the (List Nat) nil) (lambda (n-1 almost) (:: n-1 almost)))))"
          )
          -- ind-Nat
        , ( "(ind-Nat zero (lambda (k) (Vec Nat k)) vecnil (lambda (n-1 almost) (vec:: n-1 almost)))"
          , "(the (Vec Nat 0) vecnil)"
          )
        , ( "(ind-Nat 2 (lambda (k) (Vec Nat k)) vecnil (lambda (n-1 almost) (vec:: n-1 almost)))"
          , "(the (Vec Nat 2) (vec:: 1 (vec:: 0 vecnil)))"
          )
        , ( "(the (Pi ((n Nat)) (Vec Nat n)) (lambda (j) (ind-Nat j (lambda (k) (Vec Nat k)) vecnil (lambda (n-1 almost) (vec:: n-1 almost)))))"
          , "(the (Pi ((n Nat)) (Vec Nat n)) (lambda (j) (ind-Nat j (lambda (k) (Vec Nat k)) vecnil (lambda (n-1 almost) (vec:: n-1 almost)))))"
          )
          -- Σ: car and cdr
        , ( "(the (-> (Sigma ((x Atom)) (= Atom x 'syltetøj)) Atom) (lambda (p) (car p)))"
          , "(the (-> (Sigma ((x Atom)) (= Atom x 'syltetøj)) Atom) (lambda (p) (car p)))"
          )
        , ( "(car (the (Pair Nat Nat) (cons 2 3)))", "2")
        , ( "(cdr (the (Pair Nat Nat) (cons 2 3)))", "3")
        , ( "(the (Pi ((p (Sigma ((x Atom)) (= Atom x 'syltetøj)))) (= Atom (car p) 'syltetøj)) (lambda (p) (cdr p)))"
          , "(the (Pi ((p (Sigma ((x Atom)) (= Atom x 'syltetøj)))) (= Atom (car p) 'syltetøj)) (lambda (p) (cdr p)))"
          )
          -- Σ: η-expansion
        , ( "(the (-> (Pair Trivial Nat) (Pair Trivial Nat)) (lambda (x) x))"
          , "(the (-> (Pair Trivial Nat) (Pair Trivial Nat)) (lambda (x) (cons sole (cdr x))))"
          )
          -- Trivial
        , ( "(the Trivial sole)", "(the Trivial sole)")
        , ( "(the (Pi ((t1 Trivial) (t2 Trivial)) (= Trivial t1 t2)) (lambda (t1 t2) (same t1)))"
          , "(the (Pi ((t1 Trivial) (t2 Trivial)) (= Trivial t1 t2)) (lambda (t1 t2) (same sole)))"
          )
          -- Equality
        , ( "(the (= Nat 0 0) (same 0))", "(the (= Nat 0 0) (same 0))")
        , ( "(the (Pi ((n Nat)) (-> (= Nat n 0) (= Nat 0 n))) (lambda (n eq) (symm eq)))"
          , "(the (Pi ((n Nat)) (-> (= Nat n 0) (= Nat 0 n))) (lambda (n eq) (symm eq)))"
          )
        , ( "(the (Pi ((j Nat) (n Nat)) (-> (= Nat n j) (= Nat j n))) (lambda (j n eq) (replace eq (lambda (k) (= Nat k n)) (same n))))"
          , "(the (Pi ((j Nat) (n Nat)) (-> (= Nat n j) (= Nat j n))) (lambda (j n eq) (replace eq (lambda (k) (= Nat k n)) (same n))))"
          )
        , ( "((the (Pi ((j Nat) (n Nat)) (-> (= Nat n j) (= Nat j n))) (lambda (j n eq) (replace eq (lambda (k) (= Nat k n)) (same n)))) 0 0 (same 0))"
          , "(the (= Nat 0 0) (same 0))"
          )
        , ( "(the (Pi ((i Nat) (j Nat) (k Nat)) (-> (= Nat i j) (= Nat j k) (= Nat i k))) (lambda (i j k a b) (trans a b)))"
          , "(the (Pi ((i Nat) (j Nat) (k Nat)) (-> (= Nat i j) (= Nat j k) (= Nat i k))) (lambda (i j k a b) (trans a b)))"
          )
        , ( "(trans (the (= Nat 2 2) (same 2)) (the (= Nat 2 2) (same 2)))"
          , "(the (= Nat 2 2) (same 2))"
          )
        , ( "(the (-> (= Nat 0 0) (= Nat 0 0)) (lambda (eq1) (trans eq1 (the (= Nat 0 0) (same 0)))))"
          , "(the (-> (= Nat 0 0) (= Nat 0 0)) (lambda (eq1) (trans eq1 (the (= Nat 0 0) (same 0)))))"
          )
        , ( "(the (-> (= Nat 0 0) (= Nat 0 0)) (lambda (eq1) (trans (the (= Nat 0 0) (same 0)) eq1)))"
          , "(the (-> (= Nat 0 0) (= Nat 0 0)) (lambda (eq1) (trans (the (= Nat 0 0) (same 0)) eq1)))"
          )
        , ( "(the (Pi ((j Nat) (k Nat) (f (-> Nat Atom))) (-> (= Nat j k) (= Atom (f j) (f k)))) (lambda (j k f eq) (cong eq f)))"
          , "(the (Pi ((j Nat) (k Nat) (f (-> Nat Atom))) (-> (= Nat j k) (= Atom (f j) (f k)))) (lambda (j k f eq) (cong eq f)))"
          )
        , ( "(rec-List (the (List Atom) nil) 0 (lambda (_ _ l) (add1 l)))"
          , "(the Nat 0)"
          )
        , ( "(rec-List (the (List Atom) (:: 'a (:: 'b nil))) 0 (lambda (_ _ l) (add1 l)))"
          , "(the Nat 2)"
          )
        , ( "(the (Pi ((E U)) (-> (List E) Nat)) (lambda (E es) (rec-List es 0 (lambda (_ _ l) (add1 l)))))"
          , "(the (Pi ((E U)) (-> (List E) Nat)) (lambda (E es) (rec-List es 0 (lambda (_ _ l) (add1 l)))))"
          )
        , ( "(the (Pi ((P U) (S U)) (-> (Either P S) (Either S P))) (lambda (P S x) (ind-Either x (lambda (ig) (Either S P)) (lambda (l) (right l)) (lambda (r) (left r)))))"
          , "(the (Pi ((P U) (S U)) (-> (Either P S) (Either S P))) (lambda (P S x) (ind-Either x (lambda (ig) (Either S P)) (lambda (l) (right l)) (lambda (r) (left r)))))"
          )
        , ( "(the (-> Absurd (= Nat 1 2)) (lambda (x) (ind-Absurd x (= Nat 1 2))))"
          , "(the (-> Absurd (= Nat 1 2)) (lambda (x) (ind-Absurd (the Absurd x) (= Nat 1 2))))"
          )
        , ( "(the (Pi ((len Nat)) (-> (Vec Atom (add1 (add1 (add1 len)))) Atom)) (lambda (len es) (head (tail (tail es)))))"
          , "(the (Pi ((len Nat)) (-> (Vec Atom (add1 (add1 (add1 len)))) Atom)) (lambda (len es) (head (tail (tail es)))))"
          )
        , ( "(the (Pi ((len Nat) (es (Vec Atom len))) (= (Vec Atom (add1 len)) (vec:: 'prickly-pear es) (vec:: 'prickly-pear es))) (lambda (len es) (ind-Vec len es (lambda (k xs) (= (Vec Atom (add1 k)) (vec:: 'prickly-pear xs) (vec:: 'prickly-pear xs))) (same (vec:: 'prickly-pear vecnil)) (lambda (k x xs so-far) (same (vec:: 'prickly-pear (vec:: x xs)))))))"
          , "(the (Pi ((len Nat) (es (Vec Atom len))) (= (Vec Atom (add1 len)) (vec:: 'prickly-pear es) (vec:: 'prickly-pear es))) (lambda (len es) (ind-Vec len es (lambda (k xs) (= (Vec Atom (add1 k)) (vec:: 'prickly-pear xs) (vec:: 'prickly-pear xs))) (same (vec:: 'prickly-pear vecnil)) (lambda (k x xs so-far) (same (vec:: 'prickly-pear (vec:: x xs)))))))"
          )
          -- ind-List
        , ( "(the (Pi ((E U) (es (List E))) (= (List E) es (rec-List es (the (List E) nil) (lambda (x xs so-far) (:: x so-far))))) (lambda (E es) (ind-List es (lambda (xs) (= (List E) xs (rec-List xs (the (List E) nil) (lambda (y ys so-far) (:: y so-far))))) (same nil) (lambda (x xs so-far) (cong so-far (the (-> (List E) (List E)) (lambda (tl) (:: x tl))))))))"
          , "(the (Pi ((E U) (es (List E))) (= (List E) es (rec-List es (the (List E) nil) (lambda (x xs so-far) (:: x so-far))))) (lambda (E es) (ind-List es (lambda (xs) (= (List E) xs (rec-List xs (the (List E) nil) (lambda (y ys so-far) (:: y so-far))))) (same nil) (lambda (x xs so-far) (cong so-far (the (-> (List E) (List E)) (lambda (tl) (:: x tl))))))))"
          )
        , ( "((the (Pi ((E U) (es (List E))) (= (List E) es (rec-List es (the (List E) nil) (lambda (x xs so-far) (:: x so-far))))) (lambda (E es) (ind-List es (lambda (xs) (= (List E) xs (rec-List xs (the (List E) nil) (lambda (y ys so-far) (:: y so-far))))) (same nil) (lambda (x xs so-far) (cong so-far (the (-> (List E) (List E)) (lambda (tl) (:: x tl)))))))) Atom nil)"
          , "(the (= (List Atom) nil nil) (same nil))"
          )
        , ( "((the (Pi ((E U) (es (List E))) (= (List E) es (rec-List es (the (List E) nil) (lambda (x xs so-far) (:: x so-far))))) (lambda (E es) (ind-List es (lambda (xs) (= (List E) xs (rec-List xs (the (List E) nil) (lambda (y ys so-far) (:: y so-far))))) (same nil) (lambda (x xs so-far) (cong so-far (the (-> (List E) (List E)) (lambda (tl) (:: x tl)))))))) Atom (:: 'kanelsnegl nil))"
          , "(the (= (List Atom) (:: 'kanelsnegl nil) (:: 'kanelsnegl nil)) (same (:: 'kanelsnegl nil)))"
          )
        , ( "(the U (Pair Nat (Sigma ((x Nat) (f (-> Absurd Trivial Nat))) (= Nat x 13))))"
          , "(the U (Pair Nat (Sigma ((x Nat) (f (-> Absurd Trivial Nat))) (= Nat x 13))))"
          )
        , ( "(the U (-> Atom Nat (Pi ((x Nat) (y (List Nat))) (= Nat x 13))))"
          , "(the U (-> Atom Nat (Pi ((x Nat) (y (List Nat))) (= Nat x 13))))"
          )
        ]
    ]

abbrev txt = if length txt >= 40 then take 39 txt ++ "…" else txt


freshNames =
  testGroup "Freshness"
   [ testCase (concat (intersperse ", " (map (T.unpack . symbolName) used)) ++
               " ⊢ " ++ T.unpack (symbolName x) ++ " fresh ↝ " ++
               T.unpack (symbolName x'))
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
      in testCase (abbrev (show left) ++ " α≡? " ++ abbrev (show right)) $
         correct $
         case alphaEquiv left right of
           Left _ -> False
           Right _ -> True

testTick = testGroup "Validity checking of atoms" $
  [testCase ("'" ++ str ++ " OK") (mustElab (E.synth (expr (Tick (Symbol (T.pack str))))) *> pure ())
  | str <- [ "food"
           , "food---"
           , "œ"
           , "rugbrød"
           , "देवनागरी"
           , "日本語"
           , "atØm"
           , "λ"
           , "λάμβδα"
           ]
  ] ++
  [testCase ("'" ++ str ++ " not OK") (mustNotElab (E.synth (expr (Tick (Symbol (T.pack str))))))
  | str <- [ "at0m"    -- contains 0
           , "\128758" -- canoe emoji
           ]
  ]
  where expr = Expr fakeLoc
        fakeLoc = Loc "nowhere" (Pos 1 1) (Pos 2 2)

parsingSourceLocs = testGroup "Source locations from parser"
  [ testCase (show str) (parseTest str test)
  | (str, test) <- theTests
  ]
  where
    parseTest str expected =
      do res <- mustSucceed (P.parse "<test input>" P.expr str)
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
  IO e
mustFail (Left e) = return e
mustFail (Right x) =
  assertFailure ("Expected failure, but succeeded with " ++ show x)


mustParse :: P.Parser a -> String -> IO a
mustParse p e = mustSucceed (P.parse "<test input>" p e)

mustParseExpr :: String -> IO Expr
mustParseExpr = mustParse P.expr

mustElab :: E.Elab a -> IO a
mustElab act =
  mustSucceed (snd (E.runElab act None (Loc "<test suite>" (Pos 1 1) (Pos 1 1)) []))


mustNotElab :: Show a => E.Elab a -> IO ()
mustNotElab act =
  mustFail (snd (E.runElab act None (Loc "<test suite>" (Pos 1 1) (Pos 1 1)) [])) *>
  return ()

mustNotElabWith :: Show a => (ElabErr -> Bool) -> E.Elab a -> IO ()
mustNotElabWith pred act =
  do e <- mustFail (snd (E.runElab act None (Loc "<test suite>" (Pos 1 1) (Pos 1 1)) []))
     if pred e
       then return ()
       else assertFailure (show e ++ " was not the expected error")




mustBeAlphaEquiv :: Core -> Core -> IO ()
mustBeAlphaEquiv c1 c2 = mustSucceed (alphaEquiv c1 c2)

norm :: N.Norm a -> a
norm act = N.runNorm act [] None

areSame ::
  String {- ^ The input expression -} ->
  String {- ^ The supposed normal form -} ->
  Assertion
areSame input normal =
  do normStx <- mustParseExpr normal
     inputStx <- mustParseExpr input
     (E.SThe ty1 normCore) <- mustElab (E.synth normStx)
     (E.SThe ty2 inputCore) <- mustElab (E.synth inputStx)
     mustElab (E.sameType ty1 ty2)
     let v1 = norm (N.eval normCore)
     let v2 = norm (N.eval inputCore)
     mustElab (E.same ty1 v1 v2)

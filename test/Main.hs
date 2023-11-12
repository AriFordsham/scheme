{-# LANGUAGE DataKinds #-}

module Main (main) where

import Test.Hspec

import Scheme (
  SchemeError (ApplyingNonProc),
  Value (Bool, Char, Null, Number, Symbol),
  ValueEx (ValueEx),
  interpret,
  lambda,
  list,
  quote,
 )

import Evaluate (execute)

main :: IO ()
main = hspec $ do
  describe "interpreter tests" $ do
    it "cannot call a non-proc value" $
      do
        interpret
          ( list
              [Number 1, Number 2]
          )
        `shouldBe` Left ApplyingNonProc
  describe "evaluator tests" $ do
    it "Booleans evaluate to themselves" $
      execute (Bool True) `shouldBe` Right (ValueEx (Bool True))
    it "Numbers evaluate to themselves" $
      execute (Number 1) `shouldBe` Right (ValueEx (Number 1))
    it "Characters evaluate to themselves" $
      execute (Char 'a') `shouldBe` Right (ValueEx (Char 'a'))
    it "Null evaluates to itself" $
      execute Null `shouldBe` Right (ValueEx Null)
    it "car" $
      execute (list [Symbol "car", quote $ list [Symbol "a", Symbol "b", Symbol "c"]])
        `shouldBe` Right (ValueEx (Symbol "a"))
    it "nested car" $
      execute
        ( list
            [ Symbol "car"
            , list
                [ Symbol "car"
                , quote $
                    list
                      [ list [Symbol "a", Symbol "b"]
                      , list [Symbol "c", Symbol "d"]
                      ]
                ]
            ]
        )
        `shouldBe` Right (ValueEx (Symbol "a"))
    it "cdr" $
      execute
        ( list
            [Symbol "cdr", quote $ list [Symbol "a", Symbol "b", Symbol "c"]]
        )
        `shouldBe` Right (ValueEx (list [Symbol "b", Symbol "c"]))
    it "cdr of singleton is null" $
      execute (list [Symbol "cdr", quote $ list [Symbol "a"]])
        `shouldBe` Right (ValueEx Null)
    it "cons" $
      execute
        ( list
            [ Symbol "cons"
            , quote $ Symbol "a"
            , quote $ list [Symbol "b", Symbol "c"]
            ]
        )
        `shouldBe` Right (ValueEx (list [Symbol "a", Symbol "b", Symbol "c"]))
    it "null? is true for null" $
      execute (list [Symbol "null?", quote Null]) `shouldBe` Right (ValueEx (Bool True))
    it "null? is false for non-null" $
      execute (list [Symbol "null?", quote $ list [Symbol "a"]])
        `shouldBe` Right (ValueEx (Bool False))
    it "addition works" $
      execute (list [Symbol "+", Number 1, Number 1])
        `shouldBe` Right (ValueEx (Number 2))
    it "simple if" $
      execute
        ( list
            [ Symbol "if"
            , Bool True
            , quote $ Symbol "a"
            ]
        )
        `shouldBe` Right (ValueEx (Symbol "a"))
    it "if with else" $
      execute
        ( list
            [ Symbol "if"
            , Bool False
            , quote $ Symbol "a"
            , quote $ Symbol "b"
            ]
        )
        `shouldBe` Right (ValueEx (Symbol "b"))
    it "simple lambda" $
      execute
        ( list
            [ lambda ["x"] $ Symbol "x"
            , quote $ Symbol "a"
            ]
        )
        `shouldBe` Right (ValueEx (Symbol "a"))
    it "lambda with multiple arguments" $
      execute
        ( list
            [ lambda ["x", "y"] $ Symbol "y"
            , quote $ Symbol "a"
            , quote $ Symbol "b"
            ]
        )
        `shouldBe` Right (ValueEx (Symbol "b"))

    it "nested lambdas" $
      execute
        ( list
            [ list
                [ lambda ["x"] $ lambda ["y"] $ Symbol "y"
                , quote $ Symbol "a"
                ]
            , quote $ Symbol "b"
            ]
        )
        `shouldBe` Right (ValueEx (Symbol "b"))

    it "shadowed variable" $
      execute
        ( list
            [ list
                [ lambda ["x"] $ lambda ["x"] $ Symbol "x"
                , quote $ Symbol "a"
                ]
            , quote $ Symbol "b"
            ]
        )
        `shouldBe` Right (ValueEx (Symbol "b"))

    it "list function" $
      execute
        ( list
            [ Symbol "list"
            , quote $ Symbol "a"
            , quote $ Symbol "b"
            ]
        )
        `shouldBe` Right (ValueEx (list [Symbol "a", Symbol "b"]))

    it "lambda in list" $
      execute
        ( list
            [ list
                [ Symbol "car"
                , list
                    [ Symbol "list"
                    , lambda ["x"] $ Symbol "x"
                    ]
                ]
            , quote $ Symbol "a"
            ]
        )
        `shouldBe` Right (ValueEx (Symbol "a"))

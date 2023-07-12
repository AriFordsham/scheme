module Main (main) where

import Test.Hspec

import Scheme

main :: IO ()
main = hspec $ do
  it "Booleans evaluate to themselves" $
    execute (Bool True) `shouldBe` Right (Bool True)
  it "Numbers evaluate to themselves" $
    execute (Number 1) `shouldBe` Right (Number 1)
  it "Characters evaluate to themselves" $
    execute (Char 'a') `shouldBe` Right (Char 'a')
  it "Null evaluates to itself" $
    execute Null `shouldBe` Right Null
  it "car" $
    execute (list [Symbol "car", quote $ list [Symbol "a", Symbol "b", Symbol "c"]])
      `shouldBe` Right (Symbol "a")
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
      `shouldBe` Right (Symbol "a")
  it "cdr" $
    execute
      ( list
          [Symbol "cdr", quote $ list [Symbol "a", Symbol "b", Symbol "c"]]
      )
      `shouldBe` Right (list [Symbol "b", Symbol "c"])
  it "cdr of singleton is null" $
    execute (list [Symbol "cdr", quote $ list [Symbol "a"]])
      `shouldBe` Right Null
  it "cons" $
    execute
      ( list
          [ Symbol "cons"
          , quote $ Symbol "a"
          , quote $ list [Symbol "b", Symbol "c"]
          ]
      )
      `shouldBe` Right (list [Symbol "a", Symbol "b", Symbol "c"])
  it "null? is true for null" $
    execute (list [Symbol "null?", quote Null]) `shouldBe` Right (Bool True)
  it "null? is false for non-null" $
    execute (list [Symbol "null?", quote $ list [Symbol "a"]])
      `shouldBe` Right (Bool False)
  it "addition works" $
    execute (list [Symbol "+", Number 1, Number 1])
      `shouldBe` Right (Number 2)
  it "simple if" $
    execute
      ( list
          [ Symbol "if"
          , Bool True
          , quote $ Symbol "a"
          ]
      )
      `shouldBe` Right (Symbol "a")
  it "if with else" $
    execute
      ( list
          [ Symbol "if"
          , Bool False
          , quote $ Symbol "a"
          , quote $ Symbol "b"
          ]
      )
      `shouldBe` Right (Symbol "b")

module NaturalDeduction.ProofSpec where

import SpecHelper

_P,_Q,_R :: WFF
_P = Var "P"
_Q = Var "Q"
_R = Var "R"

spec :: Spec
spec = do
    describe "checkProof" $ do
        it "checks Assume correctly" $ do
            let t = Theorem [_P] (_P)
                p1 = Assume (_P)
                p2 = Assume (_Q)
            checkProof t p1 `shouldBe` (Right (_P))
            checkProof t p2 `shouldBe` Left (show (_Q) ++ " cannot be assumed")

        it "checks AndI correctly" $ do
            let t = Theorem [_P, _Q] (_P /\ _Q)
                p1 = AndI (Assume _P, Assume _Q) (_P /\ _Q)
                p2 = AndI (Assume _P, Assume _Q) (_P /\ _R)
            checkProof t p1 `shouldBe` (Right (_P /\ _Q))
            checkProof t p2 `shouldBe` Left "Could not prove (P /\\ R) from P Q"

        it "checks AndEL correctly" $ do
            let t = Theorem [_P /\ _Q] _P
                p1 = AndEL (Assume $ _P /\ _Q) _P
                p2 = AndEL (Assume $ _P /\ _Q) _Q
            checkProof t p1 `shouldBe` (Right _P)
            checkProof t p2 `shouldBe` Left "AndEL (P /\\ Q) does not prove Q"

        it "checks AndER correctly" $ do
            let t = Theorem [_P /\ _Q] _P
                p1 = AndER (Assume $ _P /\ _Q) _Q
                p2 = AndER (Assume $ _P /\ _Q) _P
            checkProof t p1 `shouldBe` (Right _Q)
            checkProof t p2 `shouldBe` Left "AndER (P /\\ Q) does not prove P"

main :: IO ()
main = hspec spec
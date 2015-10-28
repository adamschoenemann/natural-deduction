module NaturalDeduction.ProofSpec where

import SpecHelper

_A,_B,_C,_D :: WFF
_A = Var "A"
_B = Var "B"
_C = Var "C"
_D = Var "D"

_P,_Q,_R :: WFF
_P = Var "P"
_Q = Var "Q"
_R = Var "R"

false, true :: WFF
false = (Const False)
true  = (Const True)

lnot :: WFF -> WFF
lnot w = w --> false

spec :: Spec
spec = do
    describe "checkProof" $ do
        it "checks Assume correctly" $ do
            let t = Theorem [_P] (_P)
                p1 = Assume (_P)
                p2 = Assume (_Q)
            checkProof t p1 `shouldBe` (Right (_P))
            checkProof t p2 `shouldBe` Left ("Q cannot be assumed. Valid assumptions are (P)")

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

        it "checks OrIL correctly" $ do
            let t  = Theorem [_P] (_P \/ _Q)
                p1 = OrIL (Assume _P) (_P \/ _Q)
                p2 = OrIL (Assume _P) (_Q \/ _P)
            checkProof t p1 `shouldBe` Right (_P \/ _Q)
            checkProof t p2 `shouldBe` Left ("OrIL P does not prove (Q \\/ P)")

        it "checks OrIR correctly" $ do
            let t  = Theorem [_P] (_P \/ _Q)
                p1 = OrIR (Assume _P) (_Q \/ _P)
                p2 = OrIR (Assume _P) (_P \/ _Q)
            checkProof t p1 `shouldBe` Right (_Q \/ _P)
            checkProof t p2 `shouldBe` Left ("OrIR P does not prove (P \\/ Q)")

        it "checks OrE correctly" $ do
            let a = (_P /\ _Q) \/ (_P /\ _R)
                t = Theorem [a] _P
                p1 = OrE (  Assume a
                          , AndEL (Assume $ _P /\ _Q) _P
                          , AndEL (Assume $ _P /\ _R) _P
                          ) _P
                p2 = OrE (  Assume a
                          , AndEL (Assume $ _R /\ _Q) _P
                          , AndEL (Assume $ _P /\ _R) _P
                          ) _P
            checkProof t p1 `shouldBe` Right _P
            checkProof t p2 `shouldBe` Left "(R /\\ Q) cannot be assumed. Valid assumptions are ((P /\\ Q),((P /\\ Q) \\/ (P /\\ R)))"

        it "checks ImplI correctly" $ do
            let c  = (_P /\ _Q) --> _Q
                t  = Theorem [] c
                p1 = (AndER (Assume $ _P /\ _Q) _Q) `ImplI` c
                p2 = (AndER (Assume $ _P /\ _Q) _Q) `ImplI` (_P /\ _Q)
                p3 = (AndER (Assume $ _Q) _Q) `ImplI` c
            checkProof t p1 `shouldBe` Right c
            checkProof t p2 `shouldBe` Left "(P /\\ Q) is not a valid conclusion for ImplI"
            checkProof t p3 `shouldBe` Left "Q cannot be assumed. Valid assumptions are ((P /\\ Q))"

        it "checks ImplE correctly" $ do
            let c = _R
                a = [_Q /\ _P, (_P /\ _Q) --> _R]
                t = Theorem a c
                p1 =
                    (((Assume $ _Q /\ _P)
                    {-------------------} `AndER`
                              _P,                    (Assume $ _Q /\ _P)
                                                     {-----------------}`AndEL`
                                                            _Q)
                    {----------------------------------------------------------}
                                    `AndI` (_P /\ _Q) ,                             Assume $ (_P /\ _Q) --> _R)
                    {-----------------------------------------------------------------------------------------} `ImplE`
                                                            c

                p2 =
                    (((Assume $ _Q /\ _P)
                    {-------------------} `AndER`
                              _P,                    (Assume $ _Q /\ _P)
                                                     {-----------------}`AndEL`
                                                            _Q)
                    {----------------------------------------------------------}
                                    `AndI` (_P /\ _Q) ,                             Assume $ (_Q /\ _Q) --> _R)
                    {-----------------------------------------------------------------------------------------} `ImplE`
                                                            c

            checkProof t p1 `shouldBe` Right c
            checkProof t p2 `shouldBe` Left "((Q /\\ Q) --> R) cannot be assumed. Valid assumptions are ((Q /\\ P),((P /\\ Q) --> R))"

        it "checks ID correctly" $ do
            let t = Theorem [_Q, _R] _Q
                p1 = ID (Assume _Q) _Q
                p2 = ID (Assume _R) _Q

            checkProof t p1 `shouldBe` Right _Q
            checkProof t p2 `shouldBe` Left "R must be equal to Q"

            -- Proves True      (|- True)
            let t2 = Theorem [] (Const True)
                p3 = ImplI (ID (Assume false) false)
                           (false --> false)

            checkProof t2 p3 `shouldBe` Right (false --> false)

        it "checks CTR correctly" $ do
            let t = Theorem [Const False] (_P /\ _Q)
                p1  = CTR (Assume false) (_P /\ _Q)

            checkProof t p1 `shouldBe` Right (_P /\ _Q)

            let t2 = Theorem [_P, _P --> false] _Q
                p2 = CTR
                        (ImplE (Assume _P, Assume (_P --> false))
                              false)
                        _Q

            checkProof t2 p2 `shouldBe` Right _Q

        -- Proof double negation (\lnot (\lnot _Q) |- _Q)
        it "checks RAA correctly" $ do
            let t  = Theorem [(_Q --> false) --> false] _Q
                p1 = RAA (ImplE (Assume $ _Q --> false, Assume $ (_Q --> false) --> false)
                                false)
                         _Q

            checkProof t p1 `shouldBe` Right _Q

        it "checks A /\\ -A |- False correctly" $ do
            let a = _A /\ lnot _A
                t = Theorem [a] false
                p = ImplE ( AndEL (Assume a) _A
                          , AndER (Assume a) (lnot _A)
                          )
                          false

            checkProof t p `shouldBe` Right false

        it "checks A |-  -(-A) correctly" $ do
            let a = _A
                t = Theorem [a] (lnot $ lnot _A)
                p = ImplI (ImplE (Assume a, Assume $ lnot _A)
                                 false
                          )
                          (lnot $ lnot _A)

            checkProof t p `shouldBe` Right (lnot $ lnot _A)

        it "checks A, A -> B, B -> C, C -> D   |-   D   correctly" $ do
            let t = Theorem [_A, _A --> _B, _B --> _C, _C --> _D] _D
                p = (((Assume _A, Assume $ _A --> _B)
                    {--------------------------------} `ImplE`
                                  _B,                           Assume $ _B --> _C)
                    {---------------------------------------------------------------} `ImplE`
                                               _C,                                              Assume $ _C --> _D)
                    {----------------------------------------------------------------------------------------------} `ImplE`
                                                        _D

            checkProof t p  `shouldBe` Right _D

        it "checks A --> B  |-  -B --> -A   correctly (contrapositive)" $ do
            let t = Theorem [_A --> _B] (lnot _A --> lnot _B)
                p =
                    ((((Assume $ (_A --> false) --> false, Assume $ _A --> _B)
                    {----------------------------------------------------------} `ImplE`
                        ((_B --> false) --> false),                                           Assume $ _B --> false)
                    {-----------------------------------------------------------------------------------------------}`ImplE`
                                                                    false)
                    {-----------------------------------------------------------------------------------------------} `ImplI`
                                                                (_A --> false))
                    {-----------------------------------------------------------------------------------------------} `ImplI`
                                                            (lnot _B --> lnot _A)

            checkProof t p `shouldBe` Right (lnot _B --> lnot _A)

        it "checks A --> B, A --> -B   |-   -A   correctly" $ do
            let t = Theorem [_A --> _B, _A --> lnot _B] (lnot _A)
                p = ImplI (ImplE (ImplE (Assume _A, Assume $ _A --> _B)
                                        _B,
                                  ImplE (Assume _A, Assume $ _A --> lnot _B)
                                        (lnot _B)
                                 )
                                 false
                          )
                          (lnot _A)

            checkProof t p `shouldBe` Right (lnot _A)



main :: IO ()
main = hspec spec
module NaturalDeduction.Theorem where

import TruthTable

data Theorem =
    Theorem { assumptions :: [WFF]
            , conclusion :: WFF
            }
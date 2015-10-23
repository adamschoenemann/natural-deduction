module NaturalInduction.Proof where

import TruthTable
import Data.Either
import Data.String (unwords)
import Control.Monad.Error

data Theorem =
    Theorem { assumptions :: [WFF]
            , conclusion :: WFF
            }
data Proof
    = Assume WFF
    | AndI (Proof, Proof) WFF
    | AndEL Proof WFF
    | AndER Proof WFF

type CheckProofResult = Either String WFF

printProof :: Theorem -> Proof -> IO ()
printProof t p = putStrLn . (either id show) $ checkProof t p

checkProof :: Theorem -> Proof -> CheckProofResult
checkProof t p =
    case p of
        Assume w ->
            if assumed w
                then return w
                else throwError $ (show w) ++ " cannot be assumed"
        AndI (a1, a2) c -> do
            a1' <- checkProof t a1
            a2' <- checkProof t a2
            let c' = c == And a1' a2'
            if c' then return c
                  else throwError $ "Could not prove " ++ (show c) ++ " from " ++ (unwords $ map show [a1', a2'])
        AndEL a c -> do
            a' <- checkProof t a
            case a' of
                (And l _) -> if c == l then return c else throwError $ "AndEL " ++ (show a') ++ " does not prove " ++ show c
                _         -> throwError $ show a' ++ " is not a valid assumption for AndEL"
        AndER a c -> do
            a' <- checkProof t a
            case a' of
                (And _ r) -> if c == r then return c else throwError $ "AndER " ++ (show a') ++ " does not prove " ++ show c
                _         -> throwError $ show a' ++ " is not a valid assumption for AndER"

    where asmpts = assumptions t
          assumed x  = x `elem` asmpts

-- Test stuff
t1 :: Theorem
t1 = Theorem [Var "P", Var "Q"] (Var "P" /\ Var "Q")

p1 = AndI (Assume (Var "P"), Assume (Var "Z")) (Var "P" /\ Var "Q")

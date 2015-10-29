module NaturalDeduction.Proof (
    printProof, checkProof, Proof(..), Theorem(..)
) where

import TruthTable
import Data.List (intercalate)
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
    | OrIL  Proof WFF
    | OrIR  Proof WFF
    | OrE   (Proof, Proof, Proof) WFF
    | ImplI Proof WFF
    | ImplE (Proof, Proof) WFF
    | ID Proof WFF
    | CTR Proof WFF
    | RAA Proof WFF

type CheckProofResult = Either String WFF

printProof :: Theorem -> Proof -> IO ()
printProof t p = putStrLn . (either id show) $ checkProof t p

checkProof :: Theorem -> Proof -> CheckProofResult
checkProof t p =
    case p of
        Assume w ->
            if assumed w
                then return w
                else throwError $ (show w) ++ " cannot be assumed. Valid assumptions are (" ++ a ++ ")"
                     where a = intercalate "," (map show asmpts)
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
                (And _ r) -> if c == r
                             then return c
                             else throwError $ "AndER " ++ (show a') ++ " does not prove " ++ show c
                _         -> throwError $ show a' ++ " is not a valid assumption for AndER"
        OrIL a c -> do
            a' <- checkProof t a
            case c of
                a'' `Or` _ -> if a' == a''
                              then return c
                              else throwError $ "OrIL " ++ show a' ++ " does not prove " ++ show c
                _          -> throwError $ show a' ++ " is not a valid assumption for OrIL"

        OrIR a c -> do
            a' <- checkProof t a
            case c of
                _ `Or` a'' -> if a' == a''
                              then return c
                              else throwError $ "OrIR " ++ show a' ++ " does not prove " ++ show c
                _          -> throwError $ show c ++ " is not a valid assumption for OrIR"
        OrE (a1, a2, a3) c -> do
            (l `Or` r) <- checkProof t a1
            _ <- checkProof (Theorem (l:asmpts) c) a2
            _ <- checkProof (Theorem (r:asmpts) c) a3
            return c

        ImplI a c ->
            case c of
                (i `Impl` j) -> checkProof (Theorem (i:asmpts) j) a >> (return c)
                _            -> throwError $
                    show c ++ " is not a valid conclusion for ImplI"

        ImplE (a, a2) c -> do
            a'  <- checkProof t a
            a2' <- checkProof t a2
            case a2' of
                (a'' `Impl` c')
                    | c'  /= c  -> throwError $ show c'  ++ " should be " ++ show c
                    | a'' /= a' -> throwError $ show a'' ++ " should be " ++ show a'
                    | otherwise -> return c
                _   -> throwError $ show a2' ++ " is not a valid assumption for ImplE"

        ID a c -> do
            a' <- checkProof t a
            if a' == c
                then return c
                else throwError $ show a' ++ " must be equal to " ++ show c

        CTR a c -> do
            a' <- checkProof t a
            case a' of
                (Const False) -> return c
                _             -> throwError $ "False must be assumed in CTR"

        RAA a c -> do
            a' <- checkProof (Theorem ((c --> (Const False)) : asmpts) (Const False)) a
            if a' == (Const False)
                then return c
                else throwError $ "RAA must have False as the assumption"


    where asmpts = assumptions t
          assumed x  = x `elem` asmpts

-- Test stuff
-- t1 :: Theorem
-- t1 = Theorem [Var "P", Var "Q"] (Var "P" /\ Var "Q")
--
-- p1 = AndI (Assume (Var "P"), Assume (Var "Z")) (Var "P" /\ Var "Q")

# natural-deduction
A proof checker and utils for natural deduction inference

## Installing
This package depends on my [truth-table][1] package, which is not currently on hackage.

1. clone this repo
2. clone [truth-table][1]
3. `cd natural-induction`
4. `cabal sandbox init`
5. `cabal add-source ../truth-table`
6. `cabal install` (optionally also `--enable-tests`)

Now you can `cabal repl` to play with it interactively, or do whatever you want :) 

## Usage
There are two data-types exported: `Theorem` and `Proof`.
A `Theorem` conists of a list of assumptions and a conclusion.
A `Proof` can then be used to check that theorem.

The `checkProof` function can then be used to check if the proof actually hold for that theorem.

```haskell
checkProof :: Theorem -> Proof -> Either String WFF
```

`checkProof` will return an error message on failure, or the conclusion of the theorem on success.

The `WFF` data-type is found in [truth-table][1], and represents a well-formed proposition.

The `Proof` data-type is defined as such:

```haskell
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
```

## Examples
### Example 1
![T1](http://mathurl.com/pzq9dmo.png)

Proof  
![Eq1](http://mathurl.com/qxpd65u.png)

Check
```haskell
    -- using the AndI rule
    let t = Theorem [_P, _Q] (_P /\ _Q)
        p1 = AndI (Assume _P, Assume _Q) (_P /\ _Q)
        p2 = AndI (Assume _P, Assume _Q) (_P /\ _R)
    checkProof t p1 -- (Right (_P /\ _Q))
    checkProof t p2 -- Left "Could not prove (P /\\ R) from P Q"
```

### Example 2
![T2](http://mathurl.com/p2z84sk.png)

Proof  
![Eq2](http://mathurl.com/nwf84tq.png)

Check
```haskell
    -- using the AndEL rule
    let t = Theorem [_P /\ _Q] _P
        p1 = AndEL (Assume $ _P /\ _Q) _P
        p2 = AndEL (Assume $ _P /\ _Q) _Q
    checkProof t p1 -- (Right _P)
    checkProof t p2 -- Left "AndEL (P /\\ Q) does not prove Q"
```


### Example 3
Slightly more complex  
![T3](http://mathurl.com/pdctnnc.png)  

Proof  
![Eq3](http://mathurl.com/opwyaxd.png)

[1]: http://github.com/adamschoenemann/truth-table

Check
```haskell
    let a = _A
        t = Theorem [a] (lnot $ lnot _A)
        p = ImplI (ImplE (Assume a, Assume $ lnot _A)
                         false
                  )
                  (lnot $ lnot _A)

    checkProof t p `shouldBe` Right (lnot $ lnot _A)
```

### Example 4
Even more complex  
![T4](http://mathurl.com/nlzg97b.png)

Proof  
![Eq4](http://mathurl.com/o72owyf.png)


Check
```haskell
    let t = Theorem [_A, _A --> _B, _B --> _C, _C --> _D] _D
        p = (((Assume _A, Assume $ _A --> _B)
            {--------------------------------} `ImplE`
                          _B,                           Assume $ _B --> _C)
            {---------------------------------------------------------------} `ImplE`
                                       _C,                                              Assume $ _C --> _D)
            {----------------------------------------------------------------------------------------------} `ImplE`
                                                _D

    checkProof t p  `shouldBe` Right _D
```

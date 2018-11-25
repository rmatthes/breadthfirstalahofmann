module algorithmUsingRouprimeprime where

{-

    This document contains the algorithm defined using Rou''
    Verification of this algorithm is still to be done.

-}


open import Data.Nat
open import Data.List
open import Function

data Tree : Set where
  leaf : ℕ → Tree
  node : Tree → ℕ → Tree → Tree


Rou'' : Set
Rou'' = List (List ℕ)

br'' : Tree → Rou'' → Rou''
br'' (leaf n) [] = (n ∷ []) ∷ []
br'' (leaf n) (l ∷ ls) = (n ∷ l) ∷ ls
br'' (node tl n tr) []  = (n ∷ []) ∷ br'' tl (br'' tr [])
br'' (node tl n tr) (l ∷ ls)  = (n ∷ l) ∷ br'' tl (br'' tr ls)

ex'' : Rou'' → List ℕ
ex'' [] = []
ex'' (l ∷ ls) = l ++ ex'' ls

breadthfirst'' : Tree → List ℕ
breadthfirst'' t = ex'' (br'' t [])

example1 : Tree
example1  = node (leaf 2) 1 (leaf 3)

result1 : List ℕ
result1 = breadthfirst'' example1

exampleFrom4 : Tree
exampleFrom4 = node (leaf 6) 4 (leaf 7)

exampleFrom8 : Tree
exampleFrom8 = node (leaf 10) 8 (leaf 11)

exampleFrom5 : Tree
exampleFrom5 = node exampleFrom8 5 (leaf 9)

exampleFrom2 : Tree
exampleFrom2 = node exampleFrom4 2 exampleFrom5

exampleFrom1 : Tree
exampleFrom1  = node exampleFrom2 1 (leaf 3)

resultFrom1 : List ℕ
resultFrom1 = breadthfirst''  exampleFrom1

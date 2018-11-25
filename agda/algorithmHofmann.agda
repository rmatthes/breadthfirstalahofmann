module algorithmHofmann where

{-

    This document contains the algorithm by Martin Hofmann
    Verification of this algorithm is still to be done.

-}


open import Data.Nat
open import Data.List hiding (unfold)
open import Data.Vec renaming (map to mapVec ; _++_ to _++Vec_)
-- open import Data.Sum
-- open import Data.Unit
open import Data.Maybe

data Tree : Set where
  leaf : ℕ → Tree
  node : Tree → ℕ → Tree → Tree

{-# NO_POSITIVITY_CHECK #-}
data Rou : Set where
  over : Rou
  next : ((Rou → List ℕ) → List ℕ) → Rou

unfold : Rou → (Rou → List ℕ) → List ℕ
unfold over k = k over
unfold (next f) = f

br : Tree → Rou → Rou
br (leaf n) c     = next ( λ k → n ∷ unfold c k)
br (node l n r) c = next (λ k → n ∷ unfold c λ c' →
                                         k (br l (br r c')))

{-# TERMINATING #-}
ex : Rou → List ℕ
ex over = []
ex (next f) = f ex


breadthfirst : Tree → List ℕ
breadthfirst t = ex (br t over)

tree1 : Tree
tree1 = node (leaf 2) 1 (leaf 3)

result1 : List ℕ
result1 = breadthfirst tree1


{- result1 = 1 ∷ 2 ∷ 3 ∷ [] -}

tree2 : Tree
tree2 =  node (node (node (leaf 6) 4 (leaf 7)) 2 (node (node (leaf 10) 8 (leaf 11)) 5 (leaf 9))) 1 (leaf 3)

result2 : List ℕ
result2 = breadthfirst tree2

{- result2 = 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ 9 ∷ 10 ∷ 11 ∷ [] -}

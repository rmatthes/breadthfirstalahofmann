{-# OPTIONS --rewriting #-}

{-

    This document simulates the implementation of Hofmann's System
    in System F plus Mendler Recursion by using levels to simulate
    impredicativity and postulates and rewrite to simulate
    Mendler Style Fixed Points and Recursion


-}


module termVerification where



open import Data.Unit
open import Data.Nat hiding (_⊔_)
open import Data.List
open import Function
open import Level renaming (suc to lsuc ; zero to lzero)
open import Relation.Binary.PropositionalEquality

{-# BUILTIN REWRITE _≡_ #-}



data RouF {α : Level}(A : Set α ) : Set α where
  inl : ⊤ → RouF A
  inr : ((A → List ℕ) → List ℕ) → RouF A

[_,_] : {α β : Level}{A : Set α}{B : Set β} → (⊤ → B)
       → (((A → List ℕ) → List ℕ) → B)
       → RouF A → B
[ f , g ] (inl x) = f x
[ f , g ] (inr x) = g x

RouImp : {α : Level} → Set (lsuc α)
RouImp {α} = (A : Set α ) → (RouF A → A) → A

RouIt : {α : Level} (A : Set α ) → (RouF A → A) → RouImp {α} → A
RouIt A s t = t A s

RouFmap : {α β : Level}(A : Set α)(B : Set β)(h : A → B) → RouF A → RouF B
RouFmap A B h (inl u) = inl u
RouFmap A B h (inr f) = inr λ k → f (k ∘ h)

foldRouImp : {α : Level} → RouF (RouImp {α}) → RouImp {α}
foldRouImp {α} t A s = s (RouFmap (RouImp {α}) A (RouIt A s ) t)

OverImp : {α : Level} → RouImp {α}
OverImp {α} =  foldRouImp (inl tt)

NextImp : {α : Level} → ((RouImp {α} → List ℕ) → List ℕ) → RouImp {α}
NextImp {α} = foldRouImp ∘ inr

RouItImp : {α : Level}(A : Set α) → A → (((A → List ℕ) → List ℕ) → A)
                      → RouImp {α} → A
RouItImp {α} A s0 s1 = RouIt A [ (λ _ → s0) , s1 ]

postulate A' : Set
postulate s0' : A'
postulate s1' : ((A' → List ℕ) → List ℕ) → A'
postulate f' : (RouImp {lzero} → List ℕ) → List ℕ

test1 : A'
test1 = RouItImp A' s0' s1' OverImp

{- test1 = s0' -}

test2a : A'
test2a = RouItImp A' s0' s1' (NextImp f')

test2b : A'
test2b = s1' (λ k → f' (k ∘ (RouItImp {lzero} A' s0' s1')))

test2eq : test2a ≡ test2b
test2eq = refl

{- test2a =  s1' (λ k → f' (λ x → k (x A' [ (λ _ → s0') , s1' ])))

  test2b =   s1' (λ k → f' (λ x → k (x A' [ (λ _ → s0') , s1' ])))
-}


extractImp : RouImp {lzero} → List ℕ
extractImp  = RouItImp (List ℕ) [] (λ g → g (λ l → l))

test3 : List ℕ
test3 = extractImp OverImp

{- test3 = [] -}

test4a : List ℕ
test4a = extractImp (NextImp f')

test4b : List ℕ
test4b = f' extractImp

test4eq : test4a ≡ test4b
test4eq = refl
{-

test4a  = f' (λ x → x (List ℕ) [ (λ _ → []) , (λ g → g (λ l → l)) ])
test4b  = f' (λ t → t (List ℕ) [ (λ _ → []) , (λ g → g (λ l → l)) ])


-}


postulate RouMen : Set
postulate foldRouMen : RouF RouMen → RouMen


StepMen : {α β : Level}(A : Set α) → Set(α ⊔ lsuc β)
StepMen {α} {β} A =  (X : Set β)
                 → (X → RouMen) → (X → A) → RouF X → A

postulate RouRec : {α β : Level}(A : Set α) → StepMen {α} {β} A → RouMen → A


postulate rewriteRouRec : {α : Level}(A : Set α)(s : StepMen A)
                          (t : RouF RouMen) →
                         RouRec A s (foldRouMen t) ≡ s RouMen (λ x → x)(RouRec A  s) t


{-# REWRITE rewriteRouRec #-}

OverMen : {α : Level} → RouMen
OverMen {α} =  foldRouMen (inl tt)

NextMen : ((RouMen → List ℕ) → List ℕ) → RouMen
NextMen = foldRouMen ∘ inr

sextract : StepMen {lzero}{lzero} (List ℕ)
sextract X i r (inl x) = []
sextract X i r (inr f) = f r

Aunfold : Set
Aunfold = (RouMen → List ℕ) → List ℕ

sunfold : StepMen {lzero}{lzero} Aunfold
sunfold X i r (inl x) k = k (OverMen {lzero})
sunfold X i r (inr f) k = f ( k ∘ i)

extractMen : RouMen → List ℕ
extractMen = RouRec (List ℕ) sextract

unfoldMen : RouMen → Aunfold
unfoldMen = RouRec Aunfold sunfold

test5 : List ℕ
test5 = extractMen (OverMen {lzero})

{-
test5 = []

-}

postulate fmen : (RouMen → List ℕ) → List ℕ


test6a : List ℕ
test6a = extractMen (NextMen fmen)

test6b : List ℕ
test6b = fmen (RouRec (List ℕ) sextract)

test6eq : test6a ≡ test6b
test6eq = refl

{-

test6a = fmen (RouRec (List ℕ) sextract)
test6b = fmen (RouRec (List ℕ) sextract)
-}

test7 : List ℕ
test7 = extractMen (OverMen {lzero})

{-

test7 = []
-}

test8a : Aunfold
test8a = unfoldMen (NextMen fmen)

test8b : test8a ≡ fmen
test8b = refl

{-
test8a = λ k → fmen (λ x → k x)

which is eta equal to fmen
-}

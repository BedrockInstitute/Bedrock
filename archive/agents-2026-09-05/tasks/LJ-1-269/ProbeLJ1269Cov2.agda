{-# OPTIONS --cubical --safe --guardedness #-}

module LJ-1-269.ProbeLJ1269Cov2 where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_)
open import Cubical.Data.Nat.Properties using (discreteℕ; znots)
open import Cubical.Data.FinData using (Fin; toℕ)
  renaming (zero to fz; suc to fs)
open import Cubical.Data.Vec using (Vec; _∷_; []; lookup)
open import Cubical.Relation.Nullary using (Dec; yes; no)
open import Cubical.Data.Empty using (⊥; rec)

¬_ : Set → Set
¬ A = A → ⊥

w v γ K : ℕ
w = 0
v = 1
γ = 2
K = 3
δ : ℕ → ℕ
δ i = 4 + i

tgt : Vec ℕ 16
tgt = w ∷ K ∷ δ 0 ∷ δ 1 ∷ δ 2 ∷ δ 3 ∷ δ 4 ∷ δ 5
      ∷ δ 6 ∷ δ 7 ∷ δ 8 ∷ δ 9 ∷ δ 10 ∷ δ 11 ∷ v ∷ γ ∷ []

find : {n : ℕ} (s : ℕ) → Vec ℕ n → Fin (suc n)
find s []       = fz
find s (x ∷ xs) with discreteℕ s x
... | yes _ = fz
... | no  _ = fs (find s xs)

test : ¬ (toℕ (find w tgt) ≡ 16)
test with discreteℕ (toℕ (find w tgt)) 16
... | no ¬p = ¬p
... | yes p = rec (znots p)

{-# OPTIONS --cubical --safe --guardedness #-}

-- LJ-1.269 Sketch A: the named-slot layer, pure data, no reflection.
-- A slot layout as a Vec of slot names, the Fin position derived by a scan,
-- and the specimen's ρ re-expressed through it.
--
-- Slot names are ℕ codes with named constants (w, v, γ, K, δ i). This is a
-- CHOICE: decidable equality on a multi-constructor `data Slot` is not free
-- in cubical (λ () does not refute w ≡ v, because ≡ is Path), so the sketch
-- uses ℕ codes where discreteℕ supplies equality for free.

module LJ-1-269.ProbeLJ1269A where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_)
open import Cubical.Data.Nat.Properties using (discreteℕ; znots; injSuc)
open import Cubical.Data.FinData using (Fin; toℕ)
  renaming (zero to fz; suc to fs)
open import Cubical.Data.Vec using (Vec; _∷_; []; lookup)
open import Cubical.Relation.Nullary using (Dec; yes; no)
open import Cubical.Data.Empty using (⊥; rec)

¬_ : Set → Set
¬ A = A → ⊥

-- Slot names as ℕ codes.
w v γ K : ℕ
w = 0
v = 1
γ = 2
K = 3

δ : ℕ → ℕ
δ i = 4 + i

-- THE LAYOUT AS DATA: the target order of the 16 slots.
tgt : Vec ℕ 16
tgt = w ∷ K ∷ δ 0 ∷ δ 1 ∷ δ 2 ∷ δ 3 ∷ δ 4 ∷ δ 5
      ∷ δ 6 ∷ δ 7 ∷ δ 8 ∷ δ 9 ∷ δ 10 ∷ δ 11 ∷ v ∷ γ ∷ []

-- The source order (de Bruijn): w, v, γ, K, δ₀..δ₁₁.
src : Vec ℕ 16
src = w ∷ v ∷ γ ∷ K ∷ δ 0 ∷ δ 1 ∷ δ 2 ∷ δ 3 ∷ δ 4 ∷ δ 5
      ∷ δ 6 ∷ δ 7 ∷ δ 8 ∷ δ 9 ∷ δ 10 ∷ δ 11 ∷ []

-- The derived position: a scan; "not found" is the sentinel (last slot).
find : {n : ℕ} (s : ℕ) → Vec ℕ n → Fin (suc n)
find s []       = fz
find s (x ∷ xs) with discreteℕ s x
... | yes _ = fz
... | no  _ = fs (find s xs)

-- Strengthen Fin (suc n) → Fin n, given the sentinel is not hit.
strengthen : {n : ℕ} (j : Fin (suc n)) → ¬ (toℕ j ≡ n) → Fin n
strengthen {zero}  fz ¬p = rec (¬p refl)
strengthen {suc n} fz ¬p = fz
strengthen {suc n} (fs j) ¬p =
  fs (strengthen {n} j (λ e → ¬p (cong suc e)))

-- Coverage: every source slot IS in the target layout (the sentinel is
-- never hit). One refutation per source position.
covers : (i : Fin 16) → ¬ (toℕ (find (lookup i src) tgt) ≡ 16)
covers (fz) = λ e → znots (e)
covers (fs (fz)) = λ e → znots (injSuc (injSuc (injSuc (injSuc (injSuc (injSuc (injSuc (injSuc (injSuc (injSuc (injSuc (injSuc (injSuc (injSuc (e)))))))))))))))
covers (fs (fs (fz))) = λ e → znots (injSuc (injSuc (injSuc (injSuc (injSuc (injSuc (injSuc (injSuc (injSuc (injSuc (injSuc (injSuc (injSuc (injSuc (injSuc (e))))))))))))))))
covers (fs (fs (fs (fz)))) = λ e → znots (injSuc (e))
covers (fs (fs (fs (fs (fz))))) = λ e → znots (injSuc (injSuc (e)))
covers (fs (fs (fs (fs (fs (fz)))))) = λ e → znots (injSuc (injSuc (injSuc (e))))
covers (fs (fs (fs (fs (fs (fs (fz))))))) = λ e → znots (injSuc (injSuc (injSuc (injSuc (e)))))
covers (fs (fs (fs (fs (fs (fs (fs (fz)))))))) = λ e → znots (injSuc (injSuc (injSuc (injSuc (injSuc (e))))))
covers (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))) = λ e → znots (injSuc (injSuc (injSuc (injSuc (injSuc (injSuc (e)))))))
covers (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))) = λ e → znots (injSuc (injSuc (injSuc (injSuc (injSuc (injSuc (injSuc (e))))))))
covers (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))) = λ e → znots (injSuc (injSuc (injSuc (injSuc (injSuc (injSuc (injSuc (injSuc (e)))))))))
covers (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))) = λ e → znots (injSuc (injSuc (injSuc (injSuc (injSuc (injSuc (injSuc (injSuc (injSuc (e))))))))))
covers (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))) = λ e → znots (injSuc (injSuc (injSuc (injSuc (injSuc (injSuc (injSuc (injSuc (injSuc (injSuc (e)))))))))))
covers (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))) = λ e → znots (injSuc (injSuc (injSuc (injSuc (injSuc (injSuc (injSuc (injSuc (injSuc (injSuc (injSuc (e))))))))))))
covers (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))) = λ e → znots (injSuc (injSuc (injSuc (injSuc (injSuc (injSuc (injSuc (injSuc (injSuc (injSuc (injSuc (injSuc (e)))))))))))))
covers (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))) = λ e → znots (injSuc (injSuc (injSuc (injSuc (injSuc (injSuc (injSuc (injSuc (injSuc (injSuc (injSuc (injSuc (injSuc (e))))))))))))))

-- THE PERMUTATION, re-expressed through the layout.
ρ : Fin 16 → Fin 16
ρ i = strengthen (find (lookup i src) tgt) (covers i)

-- Correctness: the derived permutation is the specimen's map.
toℕρ : Fin 16 → ℕ
toℕρ i = toℕ (ρ i)

check0 : toℕρ fz ≡ 0 ; check0 = refl
check1 : toℕρ (fs fz) ≡ 14 ; check1 = refl
check2 : toℕρ (fs (fs fz)) ≡ 15 ; check2 = refl
check3 : toℕρ (fs (fs (fs fz))) ≡ 1 ; check3 = refl
check4 : toℕρ (fs (fs (fs (fs fz)))) ≡ 2 ; check4 = refl

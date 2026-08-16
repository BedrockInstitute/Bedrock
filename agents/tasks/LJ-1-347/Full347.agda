{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.347] THE WHOLE LEMMA, BOTH CLAUSES.
--
--   sgl1-not-numeral : (m : N) -> pair (# 1) (# 1) = # m -> bottom
--
-- `[LJ-1.344]` proved the `suc m` clause alone in 2.01 s
-- (`agents/tasks/LJ-1-344/Bisect344B.agda`) and could not close the
-- `zero` clause: four runs died at 330 s, 400 s, 160 s and 300 s.
-- `agents/tasks/LJ-1-347/Zero347.agda` closes the `zero` clause in
-- 1.51 s by route E, the library's `empty-empty`.
--
-- This file states the lemma over every numeral.  It is SELF CONTAINED
-- on the ambient side: it re-writes `x-in-pair` and `pair-only` rather
-- than import `agents/tasks/LJ-1-344/Supply344.agda`, so its seconds
-- figure prices the lemma and not a chapter interface.
--
-- ONE agda process under GHCRTS="-A64m -I0 -M8g".

open import Base.Prelude
open import Base.Truth

open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆; ∅; ∅-empty; pairing-ax ) renaming ( module InfinitySet to Inf )
open Inf using ( #_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ∈∈ₛ )
open import Cubical.Data.Nat using ( ℕ; zero; suc; znots )
open import Cubical.Data.Nat.Order using ( zero-≤; suc-≤-suc )
open import Cubical.Data.Sum using ( inl; inr )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )

module LJ-1-347.Full347 {ℓ : Level} where

open import V.Coding {ℓ} using ( #mono; #-inj )

-- The two ambient pair facts, four lines each, re-written because
-- src/V/Coding.lagda.md:149-150 keeps `inr-in-pair` private.  Copied
-- from agents/tasks/LJ-1-344/Supply344.agda:89-95.
x∈pair : (x y : V ℓ) → ⟨ x ∈ ⁅ x , y ⁆ ⟩
x∈pair x y =
  ∈∈ₛ {a = x} {b = ⁅ x , y ⁆} .snd (pairing-ax x y x .snd ∣ inl refl ∣₁)

pair-only : (x d : V ℓ) → ⟨ d ∈ ⁅ x , x ⁆ ⟩ → d ≡ x
pair-only x d h = PT.rec (setIsSet d x) (λ { (inl p) → p ; (inr p) → p })
  (pairing-ax x x d .fst (∈∈ₛ {a = d} {b = ⁅ x , x ⁆} .fst h))

-- =====================================================================
-- THE LEMMA.  The singleton of the numeral one is NOT a numeral.
--
-- CLAUSE `zero`, route E.  `# zero = empty` is a DEFINING equation of
-- the library's `InfinitySet`, so the subst lands in `empty` by
-- conversion.  `empty-empty` then refuses the membership as a FUNCTION.
-- Nothing transports and nothing forces an `Acc`.
--
-- CLAUSE `suc m`, `[LJ-1.344]`'s, unchanged.
-- =====================================================================

sgl1-not-numeral : (m : ℕ) → ⁅ # 1 , # 1 ⁆ ≡ # m → Empty.⊥
sgl1-not-numeral zero q =
  ∅-empty (# 1)
    (∈∈ₛ {a = # 1} {b = ∅} .fst
      (subst (λ s → ⟨ (# 1) ∈ s ⟩) q (x∈pair (# 1) (# 1))))
sgl1-not-numeral (suc m) q = znots (#-inj 0 1 zero≡one)
  where
  zero∈ : ⟨ (# 0) ∈ ⁅ # 1 , # 1 ⁆ ⟩
  zero∈ = subst (λ s → ⟨ (# 0) ∈ s ⟩) (sym q)
    (#mono 0 (suc m) (suc-≤-suc zero-≤))

  zero≡one : (# 0) ≡ (# 1)
  zero≡one = pair-only (# 1) (# 0) zero∈

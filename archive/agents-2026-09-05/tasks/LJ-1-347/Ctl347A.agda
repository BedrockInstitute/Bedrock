{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.347] CONTROL A.  IS THE IMPORT SET THE WALL, OR THE ASSEMBLY?
--
-- `Zero347.agda` proves the `zero` clause in 1.51 s with the SMALLEST
-- import set.  `Full347.agda` proves the same clause plus
-- `[LJ-1.344]`'s `suc m` clause, in ONE function with a case split on
-- `m`, and EXHAUSTS THE 8 GB HEAP at 406 s.
--
-- TWO THINGS CHANGED AT ONCE, so neither is measured yet:
--   1. `Full347.agda` adds `Base.Prelude`, `Base.Truth` and `V.Coding`.
--   2. `Full347.agda` puts the two clauses in ONE case split.
--
-- THIS FILE CHANGES ONLY (1).  It is `Zero347.agda`'s clause, alone,
-- under `Full347.agda`'s import set.  A fast exit says the import set is
-- innocent and the case split is the wall.
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

module LJ-1-347.Ctl347A {ℓ : Level} where

open import V.Coding {ℓ} using ( #mono; #-inj )

x∈pair : (x y : V ℓ) → ⟨ x ∈ ⁅ x , y ⁆ ⟩
x∈pair x y =
  ∈∈ₛ {a = x} {b = ⁅ x , y ⁆} .snd (pairing-ax x y x .snd ∣ inl refl ∣₁)

-- THE `zero` CLAUSE ALONE, under the full import set.  NO case split.
sgl1-not-zero : ⁅ # 1 , # 1 ⁆ ≡ # 0 → Empty.⊥
sgl1-not-zero q =
  ∅-empty (# 1)
    (∈∈ₛ {a = # 1} {b = ∅} .fst
      (subst (λ s → ⟨ (# 1) ∈ s ⟩) q (x∈pair (# 1) (# 1))))

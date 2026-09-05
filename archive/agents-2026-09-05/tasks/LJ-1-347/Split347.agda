{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.347] CONTROL B, AND THE CURE.  THE SAME TWO CLAUSES, NAMED.
--
-- MEASURED SO FAR:
--   `Zero347.agda`   the `zero` clause alone, small imports  0 in 1.51 s
--   `Ctl347A.agda`   the `zero` clause alone, full imports   0 in 1.70 s
--   `Bisect344B.agda` the `suc m` clause alone               0 in 2.01 s
--   `Full347.agda`   BOTH, inlined in ONE case split   HEAP OUT at 406 s
--
-- So the import set is innocent, MEASURED by `Ctl347A.agda`.  The two
-- clauses are each cheap, MEASURED three times.  What is left is the
-- ASSEMBLY: the two bodies elaborated INSIDE one case split on the
-- numeral index.  C-56 says exactly this: when a heavy proof walls, the
-- cost is in the assembly.
--
-- THIS FILE KEEPS THE CASE SPLIT AND REMOVES THE INLINING.  Each clause
-- becomes a TOP LEVEL lemma at a CLOSED index, and the split only
-- dispatches.  Nothing about the mathematics changes.
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

module LJ-1-347.Split347 {ℓ : Level} where

open import V.Coding {ℓ} using ( #mono; #-inj )

x∈pair : (x y : V ℓ) → ⟨ x ∈ ⁅ x , y ⁆ ⟩
x∈pair x y =
  ∈∈ₛ {a = x} {b = ⁅ x , y ⁆} .snd (pairing-ax x y x .snd ∣ inl refl ∣₁)

pair-only : (x d : V ℓ) → ⟨ d ∈ ⁅ x , x ⁆ ⟩ → d ≡ x
pair-only x d h = PT.rec (setIsSet d x) (λ { (inl p) → p ; (inr p) → p })
  (pairing-ax x x d .fst (∈∈ₛ {a = d} {b = ⁅ x , x ⁆} .fst h))

-- CLAUSE ONE, at the CLOSED index 0.  `Zero347.agda`'s term.
zero-clause : ⁅ # 1 , # 1 ⁆ ≡ # 0 → Empty.⊥
zero-clause q =
  ∅-empty (# 1)
    (∈∈ₛ {a = # 1} {b = ∅} .fst
      (subst (λ s → ⟨ (# 1) ∈ s ⟩) q (x∈pair (# 1) (# 1))))

-- CLAUSE TWO, at the index `suc m`.  `[LJ-1.344]`'s term, unchanged.
suc-clause : (m : ℕ) → ⁅ # 1 , # 1 ⁆ ≡ # (suc m) → Empty.⊥
suc-clause m q = znots (#-inj 0 1 zero≡one)
  where
  zero∈ : ⟨ (# 0) ∈ ⁅ # 1 , # 1 ⁆ ⟩
  zero∈ = subst (λ s → ⟨ (# 0) ∈ s ⟩) (sym q)
    (#mono 0 (suc m) (suc-≤-suc zero-≤))

  zero≡one : (# 0) ≡ (# 1)
  zero≡one = pair-only (# 1) (# 0) zero∈

-- THE DISPATCHER.  It carries no proof term of its own.
sgl1-not-numeral : (m : ℕ) → ⁅ # 1 , # 1 ⁆ ≡ # m → Empty.⊥
sgl1-not-numeral zero    = zero-clause
sgl1-not-numeral (suc m) = suc-clause m

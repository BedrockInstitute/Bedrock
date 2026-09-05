{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.347] CONTROL C.  THE TWO CLAUSES, WITHOUT THE CASE SPLIT.
--
-- MEASURED SO FAR:
--   `Zero347.agda`    `zero` clause alone, small imports   0 in 1.51 s
--   `Ctl347A.agda`    `zero` clause alone, full imports    0 in 1.70 s
--   `Bisect344B.agda` `suc m` clause alone                 0 in 2.01 s
--   `Full347.agda`    both, inlined in one split     HEAP OUT at 406 s
--   `Split347.agda`   both, named, plus a dispatcher HEAP OUT at 374 s
--
-- `Split347.agda` removed the inlining and the wall stayed.  So the
-- inlining is innocent, MEASURED.  Two suspects are left: the CASE
-- SPLIT on the numeral index, and the mere COEXISTENCE of the two
-- clauses in one module.
--
-- THIS FILE REMOVES THE CASE SPLIT AND KEEPS THE COEXISTENCE.  A fast
-- exit names the split.  A wall names the coexistence.
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

module LJ-1-347.Ctl347B {ℓ : Level} where

open import V.Coding {ℓ} using ( #mono; #-inj )

x∈pair : (x y : V ℓ) → ⟨ x ∈ ⁅ x , y ⁆ ⟩
x∈pair x y =
  ∈∈ₛ {a = x} {b = ⁅ x , y ⁆} .snd (pairing-ax x y x .snd ∣ inl refl ∣₁)

pair-only : (x d : V ℓ) → ⟨ d ∈ ⁅ x , x ⁆ ⟩ → d ≡ x
pair-only x d h = PT.rec (setIsSet d x) (λ { (inl p) → p ; (inr p) → p })
  (pairing-ax x x d .fst (∈∈ₛ {a = d} {b = ⁅ x , x ⁆} .fst h))

zero-clause : ⁅ # 1 , # 1 ⁆ ≡ # 0 → Empty.⊥
zero-clause q =
  ∅-empty (# 1)
    (∈∈ₛ {a = # 1} {b = ∅} .fst
      (subst (λ s → ⟨ (# 1) ∈ s ⟩) q (x∈pair (# 1) (# 1))))

suc-clause : (m : ℕ) → ⁅ # 1 , # 1 ⁆ ≡ # (suc m) → Empty.⊥
suc-clause m q = znots (#-inj 0 1 zero≡one)
  where
  zero∈ : ⟨ (# 0) ∈ ⁅ # 1 , # 1 ⁆ ⟩
  zero∈ = subst (λ s → ⟨ (# 0) ∈ s ⟩) (sym q)
    (#mono 0 (suc m) (suc-≤-suc zero-≤))

  zero≡one : (# 0) ≡ (# 1)
  zero≡one = pair-only (# 1) (# 0) zero∈

-- NO dispatcher.  The two clauses stand side by side and nothing splits
-- the numeral index.

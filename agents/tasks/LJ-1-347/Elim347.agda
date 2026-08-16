{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.347] THE CURE.  THE SAME SPLIT, THROUGH THE ELIMINATOR.
--
-- THE BISECTION IS COMPLETE AND IT NAMES THE SUB-TERM:
--
--   `Zero347.agda`    `zero` clause alone, small imports    0 in 1.51 s
--   `Ctl347A.agda`    `zero` clause alone, full imports     0 in 1.70 s
--   `Bisect344B.agda` `suc m` clause alone                  0 in 2.01 s
--   `Ctl347B.agda`    BOTH clauses, no split                0 in 1.73 s
--   `Split347.agda`   `Ctl347B.agda` PLUS a two line split  HEAP OUT 374 s
--   `Full347.agda`    both clauses inlined in the split     HEAP OUT 406 s
--
-- `Ctl347B.agda` and `Split347.agda` differ by TWO LINES, the
-- dispatcher.  1.73 s against an exhausted 8 GB heap.  So the explosive
-- sub-term is the PATTERN MATCH CASE SPLIT on the numeral index `m`,
-- inside a clause whose later argument has type
-- `pair (# 1) (# 1) = # m`.  It is NOT `# 0`, NOT the route, NOT the
-- import set, NOT the inlining and NOT the coexistence.  Each of those
-- five is MEASURED innocent by its own control above.
--
-- THE CURE.  Split by the LIBRARY ELIMINATOR instead.  The coverage
-- check then happens once, in `Cubical/Data/Nat/Base.agda:37-42`, at a
-- motive that mentions no set.  This file changes nothing else.
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
import Cubical.Data.Nat.Base as ℕB
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )

module LJ-1-347.Elim347 {ℓ : Level} where

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

-- THE WHOLE LEMMA.  No pattern match of mine splits the numeral index.
sgl1-not-numeral : (m : ℕ) → ⁅ # 1 , # 1 ⁆ ≡ # m → Empty.⊥
sgl1-not-numeral =
  ℕB.elim {A = λ k → ⁅ # 1 , # 1 ⁆ ≡ # k → Empty.⊥}
    zero-clause (λ m _ → suc-clause m)

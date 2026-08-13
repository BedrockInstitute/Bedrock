{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.85] probe B: the consumer's witness satisfies the repaired premise.
--
-- The real witness of hasWitnessAt is the subformula closure
--     w = clo ι ιL φ
-- (witnessAt-in, L.Coding.CodeSet.lagda.md:365-373).  This probe
-- machine-checks that w ⊆ AllCodes A: every member of the closure peels
-- (closure-inv, L.Coding.InL.lagda.md:445) to a key of a formula over the
-- carrier, and every such key lies in AllCodes A
-- (key∈AllCodes, L.Coding.CodeSet.lagda.md:443-444).  So the repaired
-- premise is available at the consumer's witness, at any carrier.
--
-- Untracked probe; one Agda process under GHCRTS="-A64m -I0 -M8g";
-- never committed.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ185B {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Coding.Closed {ℓ} using ( clo )
open import L.Coding.InL {ℓ} using ( closure-inv; key )
open import L.Coding.CodeSet {ℓ} lem using ( AllCodes; key∈AllCodes )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; ∈∈ₛ; ∈ₛ⟪_⟫↪_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )
open import Cubical.Data.Nat using ( ℕ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )

-- =====================================================================
-- AT ANY CARRIER: the closure of a formula over the carrier lies in
-- AllCodes, member by member.
-- =====================================================================
module Supply (A₀ : S) where

  ι₀ : ⟪ fst A₀ ⟫ → V ℓ
  ι₀ = ⟪ fst A₀ ⟫↪

  ι∈₀ : (m : ⟪ fst A₀ ⟫) → ⟨ ι₀ m ∈ fst A₀ ⟩
  ι∈₀ m = ∈∈ₛ {a = ι₀ m} {b = fst A₀} .snd (∈ₛ⟪ fst A₀ ⟫↪ m)

  ιL₀ : (m : ⟪ fst A₀ ⟫) → ⟨ isL (ι₀ m) ⟩
  ιL₀ m = isL-trans {x = fst A₀} {y = ι₀ m} (ι∈₀ m) (A₀ .snd)

  -- Every member of the closure is the key of some formula over the
  -- carrier (closure-inv), and every key over the carrier is in AllCodes
  -- (key∈AllCodes).  Hence the closure satisfies the repaired premise.
  clo⊆All : {n : ℕ} (φ : Formula ⟪ fst A₀ ⟫ n) (x : V ℓ)
          → ⟨ x ∈ fst (clo ι₀ ιL₀ φ) ⟩ → ⟨ x ∈ fst (AllCodes A₀) ⟩
  clo⊆All φ x hx = PT.rec (snd (x ∈ fst (AllCodes A₀))) go
    (closure-inv ι₀ ιL₀ φ x hx)
    where
    go : Σ[ m ∈ ℕ ] Σ[ ψ ∈ Formula ⟪ fst A₀ ⟫ m ]
           ((x ≡ key ι₀ ιL₀ ψ)
            × ((z : V ℓ) → ⟨ z ∈ fst (clo ι₀ ιL₀ ψ) ⟩ → ⟨ z ∈ fst (clo ι₀ ιL₀ φ) ⟩))
       → ⟨ x ∈ fst (AllCodes A₀) ⟩
    go (m , ψ , q , _) = subst (λ w → ⟨ w ∈ fst (AllCodes A₀) ⟩) (sym q)
      (key∈AllCodes A₀ ψ)

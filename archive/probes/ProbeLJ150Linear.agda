{-# OPTIONS --cubical --safe --guardedness #-}

-- LJ-1.50 probe C: the erase-to-Delta-0 certificate transfer with the
-- count proofs PROJECTED instead of re-derived by metas.  The current
-- erase-Delta-0 (src/L/BoundedSubset.lagda.md:505-517) recurses with
-- `_` metas for the subformula count proofs, which forces a countFo
-- traversal per node; this version threads plus-zero-l/plus-zero-r
-- exactly like Cnt.erase itself, so each node's work is one unfolding.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ150Linear {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import FOL.Syntax using
  ( Formula; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊤̇; ⊥̇; ∀̇∈; ∃̇∈; ∃̇_; ∀̇_ )
open import FOL.LevyHierarchy using
  ( Δ₀; δ-∈; δ-≐; δ-∧; δ-∨; δ-⇒; δ-¬; δ-⊤; δ-⊥; δ-∀∈; δ-∃∈ )
open import FOL.Manipulation.Parameters using ( countFo )
import FOL.Count
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.Condensation {ℓ} lem using ( DefBodyB; Δ₀-DefBodyB )

open hPropStructure 𝒮ᵥ
module CS = hPropStructure 𝒮ʟ

module Cnt = FOL.Count.Count {ℓ = ℓ-suc ℓ} CS.S

erase-Δ₀-lin : {m : ℕ} (φ : Formula CS.S m) (p : countFo φ ≡ 0)
             → Δ₀ φ → Δ₀ (Cnt.erase φ p)
erase-Δ₀-lin (t ∈̇ u) p δ-∈ = δ-∈
erase-Δ₀-lin (t ≐ u) p δ-≐ = δ-≐
erase-Δ₀-lin (φ ∧̇ ψ) p (δ-∧ c d) =
  δ-∧ (erase-Δ₀-lin φ (Cnt.plus-zero-l p) c)
      (erase-Δ₀-lin ψ (Cnt.plus-zero-r p) d)
erase-Δ₀-lin (φ ∨̇ ψ) p (δ-∨ c d) =
  δ-∨ (erase-Δ₀-lin φ (Cnt.plus-zero-l p) c)
      (erase-Δ₀-lin ψ (Cnt.plus-zero-r p) d)
erase-Δ₀-lin (φ ⇒̇ ψ) p (δ-⇒ c d) =
  δ-⇒ (erase-Δ₀-lin φ (Cnt.plus-zero-l p) c)
      (erase-Δ₀-lin ψ (Cnt.plus-zero-r p) d)
erase-Δ₀-lin (¬̇ φ) p (δ-¬ c) = δ-¬ (erase-Δ₀-lin φ p c)
erase-Δ₀-lin ⊤̇ p δ-⊤ = δ-⊤
erase-Δ₀-lin ⊥̇ p δ-⊥ = δ-⊥
erase-Δ₀-lin (∀̇∈ t φ) p (δ-∀∈ c) = δ-∀∈ (erase-Δ₀-lin φ (Cnt.plus-zero-r p) c)
erase-Δ₀-lin (∃̇∈ t φ) p (δ-∃∈ c) = δ-∃∈ (erase-Δ₀-lin φ (Cnt.plus-zero-r p) c)
erase-Δ₀-lin (∃̇ φ) p ()
erase-Δ₀-lin (∀̇ φ) p ()

-- The leaf at n = 0, arity 8, all sixteen slots at zero.
defb : Formula CS.S 8
defb = DefBodyB {0}
  zero zero zero zero zero zero zero zero
  zero zero zero zero zero zero zero zero

Δ₀-defb : Δ₀ defb
Δ₀-defb = Δ₀-DefBodyB {0}
  zero zero zero zero zero zero zero zero
  zero zero zero zero zero zero zero zero

-- The certificate transfer at the CONCRETE leaf, linear recursion.
transfer-concrete : Δ₀ (Cnt.erase defb refl)
transfer-concrete = erase-Δ₀-lin defb refl Δ₀-defb

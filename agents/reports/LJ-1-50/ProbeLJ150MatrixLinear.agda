{-# OPTIONS --cubical --safe --guardedness #-}

-- LJ-1.50 probe D: the erase-to-Delta-0 certificate transfer for the
-- FULL LevelHood matrix, stated directly at the concrete
-- LevelHood0.matrix, with the LINEAR recursion (count proofs
-- projected, ProbeLJ150Linear's erase-Delta-0-lin).  This gives the
-- matrix its best measured chance of a real number.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ150MatrixLinear {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import FOL.Syntax using
  ( Formula; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊤̇; ⊥̇; ∀̇∈; ∃̇∈; ∃̇_; ∀̇_ )
open import FOL.LevyHierarchy using
  ( Δ₀; δ-∈; δ-≐; δ-∧; δ-∨; δ-⇒; δ-¬; δ-⊤; δ-⊥; δ-∀∈; δ-∃∈ )
open import FOL.Manipulation.Parameters using ( countFo )
import FOL.Count
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.BoundedSubset {ℓ} lem using ( module LevelHood0 )

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

module LH0 = LevelHood0
  zero zero zero zero zero zero zero zero zero zero zero zero zero zero
  zero zero zero zero zero zero zero zero zero zero zero zero zero zero

-- The certificate transfer at the CONCRETE matrix, linear recursion.
transfer-matrix : Δ₀ (Cnt.erase LH0.matrix refl)
transfer-matrix = erase-Δ₀-lin LH0.matrix refl LH0.Δ₀-matrix

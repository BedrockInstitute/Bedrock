{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile

module K7.FunctionalValuesAtNames
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (paths : (x y : ZFStructure.S 𝒮)
    → ZFStructure._≈ˢ_ 𝒮 x y ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  (IsNm : ZFStructure.S 𝒮 → hProp ℓ)
  (_≈[G]_ _∈[G]_ : ZFStructure.S 𝒮 → ZFStructure.S 𝒮 → hProp ℓ)
  where

open import FOL.Syntax using ( Formula )
import FOL.Semantics
import K7.PossibleValues
import K7.FunctionalValues
import K7.CardinalOrder
import CardinalBridge

open TruthAlgebra (hPropAlgebra ℓ)

module PV = K7.PossibleValues 𝒮 paths
module N = PV.Names IsNm
open N using ( Nm )

𝒮ᴱ : ZFStructure (hPropAlgebra ℓ)
𝒮ᴱ = record
  { S = Nm
  ; isSetS = N.isSetNm
  ; _≈ˢ_ = λ σ τ → fst σ ≈[G] fst τ
  ; _∈ˢ_ = λ σ τ → fst σ ∈[G] fst τ }

private module SemE = FOL.Semantics (hPropAlgebra ℓ) 𝒮ᴱ
module SatE = SemE.At Nm id
open SatE using ( _⊨_ )
module CO = K7.CardinalOrder 𝒮ᴱ
module CB = CardinalBridge 𝒮ᴱ

module AtLaws
  (ext : OrdinaryProfile.Extensionality 𝒮ᴱ)
  (mem-congˡ : (σ τ ρ : Nm) → ⟨ fst σ ≈[G] fst τ ⟩
    → (fst σ ∈[G] fst ρ) ≡ (fst τ ∈[G] fst ρ))
  (mem-congʳ : (σ τ ρ : Nm) → ⟨ fst τ ≈[G] fst ρ ⟩
    → (fst σ ∈[G] fst τ) ≡ (fst σ ∈[G] fst ρ))
  where

  module FV = K7.FunctionalValues 𝒮ᴱ ext mem-congˡ mem-congʳ

  value-formula-seam : (f : Nm) → FV.valueFo f ≡ N.valueFo f
  value-formula-seam f = refl

  positive-formula-seam : (f : Nm) → FV.positiveValueFo f ≡ N.positiveValueFo f
  positive-formula-seam f = refl

  value-formulas-agree : OrdinaryProfile.Pairing 𝒮ᴱ → (f σ τ : Nm)
    → ((σ ∷ τ ∷ []) ⊨ N.positiveValueFo f) ≡ ((σ ∷ τ ∷ []) ⊨ N.valueFo f)
  value-formulas-agree = FV.value-formulas-agree

  functional-values-at-names : (f σ τ ρ : Nm)
    → ⟨ (f ∷ []) ⊨ CB.IsFunctionφ ⟩
    → ⟨ (σ ∷ τ ∷ []) ⊨ N.valueFo f ⟩
    → ⟨ (σ ∷ ρ ∷ []) ⊨ N.valueFo f ⟩
    → ⟨ fst τ ≈[G] fst ρ ⟩
  functional-values-at-names = FV.functional-formula-values

  -- The exact producer value formula occurs in this signature. This fills
  -- PreserveAtTracks.Probe.onto without a further Pairing premise.

  onto-at-names : (f a b : Nm)
    → ⟨ CO.isSurjection f a b ⟩ → (y : Nm) → ⟨ fst y ∈[G] fst b ⟩
    → ⟨ ⋁ Nm (λ x → (fst x ∈[G] fst a)
      ⊓ ((x ∷ y ∷ []) ⊨ N.valueFo f)) ⟩
  onto-at-names f a b h y = FV.surjection-value f a b y h

  module AtForcing
    (Cond : Type ℓ) (G∈ : Cond → Ω)
    (forces : ∀ {k} → Cond → Formula Nm k → Vec Nm k → Ω)
    (truth-at : ∀ {k} (φ : Formula Nm k) (ν : Vec Nm k)
      → (ν ⊨ φ) ≡ ⋁ Cond (λ r → G∈ r ⊓ forces r φ ν))
    where

    open import Cubical.HITs.PropositionalTruncation using ( ∣_∣₁ )

    -- Truth supplies soundness only for a condition in the given generic.
    -- This local statement must not be substituted for antichain determinacy,
    -- which quantifies over conditions not known to lie in that generic.

    forced-values-at-generic : (r : Cond) (f σ τ ρ : Nm) → ⟨ G∈ r ⟩
      → ⟨ forces r CB.IsFunctionφ (f ∷ []) ⟩
      → ⟨ forces r (N.valueFo f) (σ ∷ τ ∷ []) ⟩
      → ⟨ forces r (N.valueFo f) (σ ∷ ρ ∷ []) ⟩
      → ⟨ fst τ ≈[G] fst ρ ⟩
    forced-values-at-generic r f σ τ ρ h h₀ h₁ h₂ =
      functional-values-at-names f σ τ ρ
        (subst ⟨_⟩ (sym (truth-at CB.IsFunctionφ (f ∷ []))) ∣ r , h , h₀ ∣₁)
        (subst ⟨_⟩ (sym (truth-at (N.valueFo f) (σ ∷ τ ∷ []))) ∣ r , h , h₁ ∣₁)
        (subst ⟨_⟩ (sym (truth-at (N.valueFo f) (σ ∷ ρ ∷ []))) ∣ r , h , h₂ ∣₁)

{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
open import FOL.Syntax using ( Formula )
import OrdinaryProfile
import K7.CheckIndexedFamilies

module Controls.Negative.MissingCheckReading {ℓ}
  (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
    → ZFStructure._≈ˢ_ 𝒮 x y ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  (pair : OrdinaryProfile.Pairing 𝒮) (un : OrdinaryProfile.Union 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮) (sep : OrdinaryProfile.Separation 𝒮)
  (coll : OrdinaryProfile.Collection 𝒮)
  (find : OrdinaryProfile.FoundationInduction 𝒮)
  (choice : OrdinaryProfile.ChoiceSet 𝒮) (seed : ZFStructure.S 𝒮)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )
module Families = K7.CheckIndexedFamilies 𝒮 ext paths pair un pow sep coll find choice seed

module WithoutReading (β κ c p : S) (chk : S → S) (chkFo : Formula S 2)
  (body : Formula S 4)
  (mk : S → Formula S 1 → S)
  (mk-in : (b : S) (θ : Formula S 1) (a : S)
    → ⟨ a ∈ˢ b ⟩ → ⟨ (a ∷ []) ⊨ θ ⟩ → ⟨ a ∈ˢ mk b θ ⟩)
  (mk-bound : (b : S) (θ : Formula S 1) (a : S)
    → ⟨ a ∈ˢ mk b θ ⟩ → ⟨ a ∈ˢ b ⟩)
  (mk-sat : (b : S) (θ : Formula S 1) (a : S)
    → ⟨ a ∈ˢ mk b θ ⟩ → ⟨ (a ∷ []) ⊨ θ ⟩)
  where

  -- An arbitrary formula cannot fill the producer's check-graph reading.
  module Invalid = Families.AtCuts β κ c p chk chkFo
    (λ u ξ hξ → refl) body mk mk-in mk-bound mk-sat

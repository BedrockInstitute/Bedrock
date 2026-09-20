{-# OPTIONS --cubical --safe --guardedness #-}

-- K6 Track E, isolating probe. K5.ExtensionSat.Transfer alone, with no seam
-- and no K5.Structures application of this file's own, so that the cost of the
-- transfer layer is measured apart from the cost of K6/ForcesTruth.agda's four
-- applications together. Rule 5: one option set for every timing.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
open import FOL.Syntax
open import Cubical.Induction.WellFounded using ( WellFounded )
open import Cubical.HITs.PropositionalTruncation using ( ∥_∥₁ )
import OrdinaryProfile
import Valuation
import K4.Algebra
import K5.ExtensionSat

module K6.ProbeE4
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (carrier : ZFStructure.S 𝒮)
  (B : ZFStructure.S 𝒮)
  (L : K4.Algebra.Lattice 𝒮 B)
  (IsNameᴾ IsNameᴮ : ZFStructure.S 𝒮 → hProp ℓ)
  where

open import FOL.ZFStructure using ( module hPropStructure )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

open K4.Algebra 𝒮 using ( Pt )
open Valuation 𝒮 using ( Conditions )

module Kernel
  (entry       : S → S → S)
  (Child       : S → S → Type ℓ)
  (isPropChild : (x n : S) → isProp (Child x n))
  (child-entry : (x b n : S) → ⟨ entry x b ∈ˢ n ⟩ → Child x n)
  (child-wf    : WellFounded Child)
  (∅ᴺ          : S)
  (∅ᴺ-spec     : (z : S) → (z ∈ˢ ∅ᴺ) ≡ ⊥)
  (_≼ᶜ_        : Conditions carrier → Conditions carrier → Ω)
  (≼ᶜ-refl     : (p : Conditions carrier) → ⟨ p ≼ᶜ p ⟩)
  (≼ᶜ-trans    : {p q r : Conditions carrier} → ⟨ p ≼ᶜ q ⟩ → ⟨ q ≼ᶜ r ⟩ → ⟨ p ≼ᶜ r ⟩)
  (inhabitedᶜ  : ∥ Conditions carrier ∥₁)
  (child-nameᴾ : (n : S) → ⟨ IsNameᴾ n ⟩ → (x : S) → Child x n → ⟨ IsNameᴾ x ⟩)
  (child-nameᴮ : (n : S) → ⟨ IsNameᴮ n ⟩ → (x : S) → Child x n → ⟨ IsNameᴮ x ⟩)
  where

  module ES = K5.ExtensionSat.Transfer 𝒮
                entry Child isPropChild child-entry child-wf ∅ᴺ ∅ᴺ-spec
                carrier _≼ᶜ_ ≼ᶜ-refl ≼ᶜ-trans inhabitedᶜ IsNameᴾ child-nameᴾ
                B L IsNameᴮ child-nameᴮ

  module At (G : Conditions carrier → Ω) (U : Pt B → Ω) where
    module EA = ES.At G U

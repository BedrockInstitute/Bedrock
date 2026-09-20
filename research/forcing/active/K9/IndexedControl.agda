{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile

module K9.IndexedControl
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (families : NameKernel.Families 𝒮)
  (accessible : NameKernel.Accessibility 𝒮)
  (images : NameKernel.MemberImage 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (κ w : ZFStructure.S 𝒮)
  where

open import FOL.ZFStructure using ( module hPropStructure )
import GroundDescription
import K9.NameGround
import K9.IndexedNames

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
private
  module NG = K9.NameGround 𝒮 families accessible images pow κ w
  module I = K9.IndexedNames 𝒮 families accessible images pow κ w
  module Description = GroundDescription 𝒮 NG.extensional NG.≈ˢ-paths

indexed-check : (A : S) → I.indexedCode A NG.Check.chk ≡ NG.Check.chk A
indexed-check A = Description.ext-path
  (λ e → I.indexed-spec A NG.Check.chk e ∙ sym (NG.Check.chk-spec A e))

module AtGeneric (G : NG.P.Sub) (positive : ⟨ NG.P.positive G ⟩) where
  private
    module At = NG.AtGeneric G
    module IV = I.AtGeneric G positive
  check-member : (A χ : S) → (χ At.E.∈[G] NG.Check.chk A)
    ≡ ⋁ S (λ a → (a ∈ˢ A) ⊓ (χ At.E.≈[G] NG.Check.chk a))
  check-member A χ = cong (χ At.E.∈[G]_) (sym (indexed-check A))
    ∙ IV.indexed-value A NG.Check.chk χ

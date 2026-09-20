{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile
import Cubical.HITs.PropositionalTruncation as PT
import K10.CohenBooleanInjMaps

-- First extraction layer: only the two bounded existentials and prAtˢ.
-- Does not unfold hitInner (order or memAtˢ).

module K10.CohenBooleanInjRn
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (families : NameKernel.Families 𝒮)
  (accessible : NameKernel.Accessibility 𝒮)
  (images : NameKernel.MemberImage 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (κ w : ZFStructure.S 𝒮)
  (lem : LEM ℓ)
  (paths : (x y : ZFStructure.S 𝒮)
         → (ZFStructure._≈ˢ_ 𝒮 x y) ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
open import CodedVocabulary 𝒮 using ( isKPairΔ )
open PT using ( ∣_∣₁ ; ∥_∥₁ ; squash₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )

module Maps = K10.CohenBooleanInjMaps 𝒮 families accessible images pow κ w lem paths
open Maps using ( hitFo ; hit-reading ; hitCoreB ; hitInner )

hit-rn : (σ p ω₁ y ξ : S)
  → ⟨ (y ∷ ξ ∷ []) ⊨ hitFo σ p ω₁ ⟩
  → ∥ Σ[ r ∈ S ] Σ[ n ∈ S ]
      (⟨ r ∈ˢ Maps.Chk.carrier ⟩ × ⟨ n ∈ˢ w ⟩ × ⟨ isKPairΔ y r n ⟩
       × ⟨ (n ∷ r ∷ y ∷ ξ ∷ p ∷ σ ∷ Maps.BAT.B ∷ []) ⊨ hitInner ω₁ ⟩) ∥₁
hit-rn σ p ω₁ y ξ h =
  PT.rec squash₁
    (λ { (r , r∈c , hn) →
      PT.rec squash₁
        (λ { (n , n∈w , ypn , inner) →
          ∣ r , n , r∈c , n∈w , ypn , inner ∣₁ })
        hn })
    (subst ⟨_⟩ (hit-reading σ p ω₁ y ξ) h)

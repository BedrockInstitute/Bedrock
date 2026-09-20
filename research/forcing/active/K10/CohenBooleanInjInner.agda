{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile
import Cubical.HITs.PropositionalTruncation as PT
import K10.CohenBooleanInjMaps

-- Second extraction layer: from hitInner, the order conjunct and the
-- unevaluated hitMem. Does not unfold memAtˢ.

module K10.CohenBooleanInjInner
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
open import CodedVocabulary 𝒮 using ( isKPairΔ ; refinesΔ )
open PT using ( ∣_∣₁ ; ∥_∥₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )

module Maps = K10.CohenBooleanInjMaps 𝒮 families accessible images pow κ w lem paths
open Maps using ( hitInner ; hitMem )

inner-env : (n r y ξ p σ B : S) → _
inner-env n r y ξ p σ B = n ∷ r ∷ y ∷ ξ ∷ p ∷ σ ∷ B ∷ []

hit-order-mem : (ω₁ n r y ξ p σ B : S)
  → ⟨ (inner-env n r y ξ p σ B) ⊨ hitInner ω₁ ⟩
  → ⟨ refinesΔ Maps.Chk.order r p ⟩
    × ⟨ (inner-env n r y ξ p σ B) ⊨ hitMem ω₁ ⟩
hit-order-mem ω₁ n r y ξ p σ B (ord , mem) = ord , mem

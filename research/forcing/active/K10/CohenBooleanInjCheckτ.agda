{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile
import K10.CohenBooleanInjMaps

-- Convert the 10-slot checks conjunct of hitAtom into τ ≈ check(pair).
-- Isolated from Compile and from memAtˢ-reading.

module K10.CohenBooleanInjCheckτ
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
open import CodedVocabulary 𝒮 using ( isKPairΔ ; instFo ; Fits ; ⊨-inst )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )

module Maps = K10.CohenBooleanInjMaps 𝒮 families accessible images pow κ w lem paths
open Maps using ( checkPair ; pairDom )

atom-env : (b τ pair n r y ξ p σ B : S) → _
atom-env b τ pair n r y ξ p σ B =
  b ∷ τ ∷ pair ∷ n ∷ r ∷ y ∷ ξ ∷ p ∷ σ ∷ B ∷ []

open-checks : (ω₁ b τ pair n r y ξ p σ B : S)
  → ⟨ atom-env b τ pair n r y ξ p σ B
        ⊨ instFo checkPair (Maps.Chk.checks (pairDom ω₁)) ⟩
  → ⟨ (τ ∷ pair ∷ []) ⊨ Maps.Chk.checks (pairDom ω₁) ⟩
open-checks ω₁ b τ pair n r y ξ p σ B h =
  subst ⟨_⟩
    (⊨-inst checkPair (Maps.Chk.checks (pairDom ω₁))
      (atom-env b τ pair n r y ξ p σ B) (τ ∷ pair ∷ []) fits)
    h
  where
  fits : Fits checkPair (atom-env b τ pair n r y ξ p σ B) (τ ∷ pair ∷ [])
  fits zero = refl
  fits (suc zero) = refl

τ-is-check : (ω₁ ξ n pair τ : S)
  → ⟨ ξ ∈ˢ ω₁ ⟩ → ⟨ n ∈ˢ w ⟩ → ⟨ isKPairΔ pair ξ n ⟩
  → ⟨ (τ ∷ pair ∷ []) ⊨ Maps.Chk.checks (pairDom ω₁) ⟩
  → ⟨ τ ≈ˢ Maps.Chk.check pair ⟩
τ-is-check ω₁ ξ n pair τ hξ hn hpair h =
  subst ⟨_⟩ (Maps.Chk.checks-reading (pairDom ω₁) τ pair pair∈) h
  where
  pair∈ : ⟨ pair ∈ˢ pairDom ω₁ ⟩
  pair∈ = subst (λ t → ⟨ t ∈ˢ pairDom ω₁ ⟩)
    (sym (Maps.Chk.ordered-unique pair ξ n hpair))
    (Maps.Chk.product-in ω₁ w ξ n hξ hn)

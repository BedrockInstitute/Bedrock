{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile
import Cubical.HITs.PropositionalTruncation as PT
import K10.CohenBooleanInjMaps

-- Third extraction layer: the three unbounded existentials of hitMem.
-- Leaves hitAtom uninterpreted.

module K10.CohenBooleanInjTriple
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
open PT using ( ∣_∣₁ ; ∥_∥₁ ; squash₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )

module Maps = K10.CohenBooleanInjMaps 𝒮 families accessible images pow κ w lem paths
open Maps using ( hitMem ; hitAtom )

atom-env : (b τ pair n r y ξ p σ B : S) → _
atom-env b τ pair n r y ξ p σ B =
  b ∷ τ ∷ pair ∷ n ∷ r ∷ y ∷ ξ ∷ p ∷ σ ∷ B ∷ []

hit-triple : (ω₁ n r y ξ p σ B : S)
  → ⟨ (n ∷ r ∷ y ∷ ξ ∷ p ∷ σ ∷ B ∷ []) ⊨ hitMem ω₁ ⟩
  → ∥ Σ[ pair ∈ S ] Σ[ τ ∈ S ] Σ[ b ∈ S ]
      ⟨ atom-env b τ pair n r y ξ p σ B ⊨ hitAtom ω₁ ⟩ ∥₁
hit-triple ω₁ n r y ξ p σ B h =
  PT.rec squash₁
    (λ { (pair , hτ) →
      PT.rec squash₁
        (λ { (τ , hb) →
          PT.rec squash₁
            (λ { (b , hatom) →
              ∣ pair , τ , b , hatom ∣₁ })
            hb })
        hτ })
    h

{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile
import K10.CohenBooleanCands
import K10.CohenBooleanSubset

module K10.CohenBooleanPower
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (families : NameKernel.Families 𝒮)
  (accessible : NameKernel.Accessibility 𝒮)
  (images : NameKernel.MemberImage 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (κ w : ZFStructure.S 𝒮)
  (lem : LEM ℓ)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open NameKernel.MemberImage images using ( image ; image-spec )

module Cands = K10.CohenBooleanCands 𝒮 families accessible images pow κ w
module Sub = K10.CohenBooleanSubset 𝒮 families accessible images pow κ w lem

powerB : S
powerB = image Cands.cands (λ p → Sub.candEntry (fst p))

powerB-spec : (e : S)
  → (e ∈ˢ powerB)
    ≡ ⋁ S (λ σ → ⋁ ⟨ σ ∈ˢ Cands.cands ⟩ (λ _ → e ≈ˢ Sub.candEntry σ))
powerB-spec e = image-spec Cands.cands (λ p → Sub.candEntry (fst p)) e

{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile
import K4.Algebra
import K9.BooleanAtomic
import K10.CohenBooleanMiximalLeft
import K10.CohenBooleanMiximalMem
import K10.CohenBooleanPower
import K10.CohenBooleanSubset

module K10.CohenBooleanSubsetMem
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

module L = K10.CohenBooleanMiximalLeft 𝒮 families accessible images pow κ w lem
module MM = K10.CohenBooleanMiximalMem 𝒮 families accessible images pow κ w lem
module Sub = K10.CohenBooleanSubset 𝒮 families accessible images pow κ w lem
module Power = K10.CohenBooleanPower 𝒮 families accessible images pow κ w lem
module BAT = K9.BooleanAtomic.Atomic 𝒮 families accessible images pow κ w lem
  using ( _∈ᴮ_ )
open K4.Algebra 𝒮 using ( _≤ᴮ_ ; ⊆ˢ-trans )

opaque
  subsetVal≤mem : (τ : S)
    → ⟨ Sub.subsetVal τ ≤ᴮ BAT._∈ᴮ_ τ Power.powerB ⟩
  subsetVal≤mem τ = ⊆ˢ-trans (L.covering τ) (MM.miximal-member-ub τ)

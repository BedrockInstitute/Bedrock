{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile
import K4.Algebra

module K10.CohenBooleanPowerTop
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

import K10.CohenBooleanPowerUnfold
import K10.CohenBooleanPowerSub
import K10.CohenBooleanSubsetMem
import K10.CohenBooleanNamed

module Unfold = K10.CohenBooleanPowerUnfold 𝒮 families accessible images pow
  κ w lem paths
  using ( module VS ; module PS ; module BAT ; omegaNm ; emptyEnv ; at2
        ; inner ; inner-top-from ; module FromAll )
module Subset = K10.CohenBooleanPowerSub 𝒮 families accessible images pow
  κ w lem paths
  using ( subsetVal≡compiled ; member≤subset )
module Member = K10.CohenBooleanSubsetMem 𝒮 families accessible images pow κ w lem
  using ( subsetVal≤mem )
module Named = K10.CohenBooleanNamed 𝒮 families accessible images pow κ w lem
  using ( powerNm )

open K4.Algebra 𝒮 using ( _≤ᴮ_ )
open Unfold.VS using ( Nameᴮ ; val )
open K4.Algebra.Lattice Unfold.BAT.IC.codedLattice using ( ⊤ᴮ )
open Unfold.BAT.Atomic using () renaming ( _∈ᴮ_ to mem )

subset-member : (τ : Nameᴮ)
  → ⟨ val Unfold.PS.subsetSrc (τ ∷ Unfold.omegaNm ∷ Unfold.emptyEnv)
      ≤ᴮ mem (fst τ) (fst Named.powerNm) ⟩
subset-member τ = subst
  (λ b → ⟨ b ≤ᴮ mem (fst τ) (fst Named.powerNm) ⟩)
  (Subset.subsetVal≡compiled τ) (Member.subsetVal≤mem (fst τ))

inner-top : (τ : Nameᴮ)
  → val Unfold.inner (τ ∷ Unfold.at2 Named.powerNm) ≡ ⊤ᴮ
inner-top τ = Unfold.inner-top-from Named.powerNm τ
  (Subset.member≤subset τ) (subset-member τ)

module Result = Unfold.FromAll Named.powerNm inner-top using ( power-top )

power-top : val Unfold.PS.powerSrc (Unfold.at2 Named.powerNm) ≡ ⊤ᴮ
power-top = Result.power-top

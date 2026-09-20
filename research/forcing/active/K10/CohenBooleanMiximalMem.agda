{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile
import K4.Algebra
import K9.BooleanAtomic
import K9.BooleanNameGround
import K10.CohenBooleanCands
import K10.CohenBooleanMiximal
import K10.CohenBooleanPower
import K10.CohenBooleanPowerMem
import K10.CohenBooleanSubset

module K10.CohenBooleanMiximalMem
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

module Mx = K10.CohenBooleanMiximal 𝒮 families accessible images pow κ w lem
module PM = K10.CohenBooleanPowerMem 𝒮 families accessible images pow κ w lem
module Sub = K10.CohenBooleanSubset 𝒮 families accessible images pow κ w lem
module Power = K10.CohenBooleanPower 𝒮 families accessible images pow κ w lem
module BNG = K9.BooleanNameGround 𝒮 families accessible images pow κ w lem
open BNG using ( module Translation ; module IC )
module BAT = K9.BooleanAtomic.Atomic 𝒮 families accessible images pow κ w lem
  using ( _∈ᴮ_ ; _≈ᴮ_ )
open K4.Algebra 𝒮 using ( Pt ; _≤ᴮ_ )
open K4.Algebra.Lattice IC.codedLattice using ( _⊓ᴮ_ )

opaque
  miximal-member-ub : (τ : S)
    → ⟨ (Sub.subsetVal (Translation.trᴮ (Mx.miximalOf τ))
          ⊓ᴮ BAT._≈ᴮ_ τ (Translation.trᴮ (Mx.miximalOf τ)))
        ≤ᴮ BAT._∈ᴮ_ τ Power.powerB ⟩
  miximal-member-ub τ =
    PM.member-ub τ (Mx.miximalOf τ) (Mx.miximal-in-cands τ)

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
import K10.CohenBooleanMiximal
import K10.CohenBooleanPower
import K10.CohenBooleanPowerSrc
import K10.CohenBooleanPowerSub
import K10.CohenBooleanSubset

module K10.CohenBooleanSubsetLe
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

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

module PS = K10.CohenBooleanPowerSub 𝒮 families accessible images pow κ w lem paths
module Mx = K10.CohenBooleanMiximal 𝒮 families accessible images pow κ w lem
module Sub = K10.CohenBooleanSubset 𝒮 families accessible images pow κ w lem
module Power = K10.CohenBooleanPower 𝒮 families accessible images pow κ w lem
module Src = K10.CohenBooleanPowerSrc 𝒮
module BNG = K9.BooleanNameGround 𝒮 families accessible images pow κ w lem
open BNG using ( module Translation ; module IC )
module BAT = K9.BooleanAtomic.Atomic 𝒮 families accessible images pow κ w lem
  using ( _∈ᴮ_ ; _≈ᴮ_ )
open K4.Algebra 𝒮 using ( Pt ; _≤ᴮ_ ; ⊆ˢ-trans )
open K4.Algebra.Lattice IC.codedLattice using ( _⊓ᴮ_ )

opaque
  subset≤mem-from : (τ : PS.VS.Nameᴮ)
    → ⟨ Sub.subsetVal (fst τ)
        ≤ᴮ (Sub.subsetVal (Translation.trᴮ (Mx.miximalOf (fst τ)))
            ⊓ᴮ BAT._≈ᴮ_ (fst τ) (Translation.trᴮ (Mx.miximalOf (fst τ)))) ⟩
    → ⟨ PS.VS.val Src.subsetSrc (τ ∷ PS.omegaNm ∷ PS.emptyEnv)
        ≤ᴮ BAT._∈ᴮ_ (fst τ) Power.powerB ⟩
  subset≤mem-from τ hyp =
    ⊆ˢ-trans
      (subst (λ z → ⟨ z ≤ᴮ (Sub.subsetVal (Translation.trᴮ (Mx.miximalOf (fst τ)))
                            ⊓ᴮ BAT._≈ᴮ_ (fst τ) (Translation.trᴮ (Mx.miximalOf (fst τ)))) ⟩)
        (PS.subsetVal≡compiled τ) hyp)
      (PS.member-ub (fst τ) (Mx.miximalOf (fst τ)) (Mx.miximal-in-cands (fst τ)))

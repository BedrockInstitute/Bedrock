{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile
import K4.Algebra
import K4.Implication
import K9.BooleanAtomic
import K9.BooleanNameGround
import K10.CohenBooleanMiximal
import K10.CohenBooleanMiximalCover
import K10.CohenBooleanSubset

module K10.CohenBooleanMiximalApprox
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
module Cv = K10.CohenBooleanMiximalCover 𝒮 families accessible images pow κ w lem
module Sub = K10.CohenBooleanSubset 𝒮 families accessible images pow κ w lem
module BNG = K9.BooleanNameGround 𝒮 families accessible images pow κ w lem
open BNG using ( B ; weight ; module Translation ; module BSupport ; module IC )
module BAT = K9.BooleanAtomic.Atomic 𝒮 families accessible images pow κ w lem
  using ( _∈ᴮ_ ; _≈ᴮ_ ; ≈ᴮ-glb )
open K4.Algebra 𝒮 using ( Pt ; _≤ᴮ_ ; ⊆ˢ-trans )
open K4.Algebra.Lattice IC.codedLattice using ( _⊓ᴮ_ ; ⊓-glb ; ⊓-lb₁ ; ⊓-lb₂ )
open K4.Implication 𝒮 BNG.NG.extensional BNG.NG.≈ˢ-paths B IC.codedLattice
  IC.codedComplement
  using ( _⇒ᴮ_ )

miximalNm : S → S
miximalNm τ = Translation.trᴮ (Mx.miximalOf τ)

module FromLeft
  (left : (τ x : S) → ⟨ x ∈ˢ BSupport.support τ ⟩
        → ⟨ Sub.subsetVal τ
            ≤ᴮ (weight τ x ⇒ᴮ BAT._∈ᴮ_ x (miximalNm τ)) ⟩)
  where

  opaque
    approx-eq : (τ : S)
      → ⟨ Sub.subsetVal τ ≤ᴮ BAT._≈ᴮ_ τ (miximalNm τ) ⟩
    approx-eq τ = BAT.≈ᴮ-glb τ (miximalNm τ) (Sub.subsetVal τ)
      (left τ)
      (λ y hy → Cv.miximal-right τ y (Sub.subsetVal τ) hy)

  opaque
    approx-meet : (τ : S)
      → ⟨ Sub.subsetVal τ ≤ᴮ Sub.subsetVal (miximalNm τ) ⟩
      → ⟨ Sub.subsetVal τ
          ≤ᴮ (Sub.subsetVal (miximalNm τ) ⊓ᴮ BAT._≈ᴮ_ τ (miximalNm τ)) ⟩
    approx-meet τ hyp-sub =
      ⊓-glb (Sub.subsetVal (miximalNm τ)) (BAT._≈ᴮ_ τ (miximalNm τ))
        (Sub.subsetVal τ) hyp-sub (approx-eq τ)

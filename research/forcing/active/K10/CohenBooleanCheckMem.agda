{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile
import Cubical.HITs.PropositionalTruncation as PT
import K4.CheckValues
import K9.BooleanNameGround
import K9.BooleanAtomic

module K10.CohenBooleanCheckMem
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (families : NameKernel.Families 𝒮)
  (accessible : NameKernel.Accessibility 𝒮)
  (images : NameKernel.MemberImage 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (κ w : ZFStructure.S 𝒮)
  (lem : LEM ℓ)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open PT using ( ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

module BNG = K9.BooleanNameGround 𝒮 families accessible images pow κ w lem
open BNG using ( B ; weight ; weight-upper ; weight-least ; module NG
               ; module IC ; module BK ; module BSupport ; module Checked )
open NG using ( extensional ; ≈ˢ-paths )
module BAT = K9.BooleanAtomic 𝒮 families accessible images pow κ w lem
  using ( module Atomic ; module Laws )

module Values = K4.CheckValues.Core.Names.Values 𝒮 extensional ≈ˢ-paths
  B IC.codedLattice IC.codedComplement IC.codedComplete
  BK.Child BK.RawRec.result BSupport.support BSupport.support-out weight
  BK.entry BK.entry-inj (λ x b n h → ∣ b , h ∣₁) (λ x n h → h)
  BK.IsName BSupport.support-in weight-upper weight-least
  Checked.check Checked.check-spec Checked.check-name
  BAT.Atomic._≈ᴮ_ BAT.Atomic._∈ᴮ_
  BAT.Atomic.∈ᴮ-ub BAT.Atomic.∈ᴮ-lub
  BAT.Atomic.≈ᴮ-lbˡ BAT.Atomic.≈ᴮ-lbʳ BAT.Atomic.≈ᴮ-sym
  BAT.Laws.≈ᴮ-refl BAT.Laws.≈ᴮ-trans BAT.Laws.ext-≈ᴮ BAT.Laws.∈ᴮ-empty
  using ( check-∈-top ; check-∈-ub ; check-∈-lub )

check-∈-top = Values.check-∈-top
check-∈-ub = Values.check-∈-ub
check-∈-lub = Values.check-∈-lub

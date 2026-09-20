{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile
import CardinalBridge

module K9.Theorem
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (families : NameKernel.Families 𝒮)
  (accessible : NameKernel.Accessibility 𝒮)
  (images : NameKernel.MemberImage 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (find : OrdinaryProfile.FoundationInduction 𝒮)
  (κ w : ZFStructure.S 𝒮)
  (lem : LEM ℓ)
  (hw : ⟨ CardinalBridge.isOmega 𝒮 w ⟩)
  where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Semantics
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )
import K9.NameGround
import K9.RealValues
import K9.GraphNames
import K9.GraphInjection

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
module Ground = K9.NameGround 𝒮 families accessible images pow κ w
  using ( module K; module P; module PS )
private
  module Reals = K9.RealValues 𝒮 families accessible images pow find κ w lem hw
    using ( module GB; module AtGeneric )
  module Graph = K9.GraphNames 𝒮 families accessible images pow κ w
    using ( graph; graphCode; checkNm; graphSupport; graph-support )
  module GraphProof = K9.GraphInjection 𝒮 families accessible images pow κ w
    using ( module Injection )

open Graph public using ( graph; graphCode; checkNm; graphSupport; graph-support )

module AtGeneric
  (G : Ground.P.Sub)
  (generic : Reals.GB.Completion.isGeneric G)
  where

  extension : ZFStructure (hPropAlgebra ℓ)
  extension = Ground.PS.𝒮ᴾ[ G ]

  module CB = CardinalBridge extension
    using ( isPowerSet; isInjection; injectable; IsInjectionφ; IsInjection-bridge )
  private
    module RV = Reals.AtGeneric G generic
      using ( positive; filter; real-subset-check; real-values-distinct
            ; real-membership-spec; checked-natural-membership; module Bits )
    module GI = GraphProof.Injection G RV.positive RV.filter
      using ( graph-value; graph-domain; isInjection )
    module Sem = FOL.Semantics (hPropAlgebra ℓ) extension
  open Sem.At Ground.K.Name id using () renaming ( _⊨_ to _⊨ᴱ_ )
  open RV public using ( real-subset-check; real-values-distinct
                      ; real-membership-spec; checked-natural-membership )
  open RV.Bits public using ( bit-total; bit-total₀₁; bit-functional )
  open GI public using ( graph-value; graph-domain )

  injection-at-power : (Y : Ground.K.Name)
    → ⟨ CB.isPowerSet Y (checkNm w) ⟩
    → ⟨ CB.isInjection graph (checkNm κ) Y ⟩
  injection-at-power = GI.isInjection lem RV.real-subset-check RV.real-values-distinct

  injection-satisfaction : (Y : Ground.K.Name)
    → ⟨ CB.isPowerSet Y (checkNm w) ⟩
    → ⟨ (graph ∷ checkNm κ ∷ Y ∷ []) ⊨ᴱ CB.IsInjectionφ ⟩
  injection-satisfaction Y powerY = subst ⟨_⟩
    (sym (CB.IsInjection-bridge graph (checkNm κ) Y)) (injection-at-power Y powerY)

  internal-injection : OrdinaryProfile.PowerSet extension
    → ⟨ ⋁ Ground.K.Name (λ Y → CB.isPowerSet Y (checkNm w)
      ⊓ CB.isInjection graph (checkNm κ) Y) ⟩
  internal-injection extensionPower = PT.map
    (λ { (Y , powerY) → Y , powerY , injection-at-power Y powerY })
    (extensionPower (checkNm w))

  internal-cardinal-comparison : OrdinaryProfile.PowerSet extension
    → ⟨ ⋁ Ground.K.Name (λ Y → CB.isPowerSet Y (checkNm w)
      ⊓ CB.injectable (checkNm κ) Y) ⟩
  internal-cardinal-comparison extensionPower = PT.map
    (λ { (Y , powerY , inject) → Y , powerY , ∣ graph , inject ∣₁ })
    (internal-injection extensionPower)

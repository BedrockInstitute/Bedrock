{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile

module K8.Theorem
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
    → ZFStructure._≈ˢ_ 𝒮 x y ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  (pair : OrdinaryProfile.Pairing 𝒮)
  (un : OrdinaryProfile.Union 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (sep : OrdinaryProfile.Separation 𝒮)
  (coll : OrdinaryProfile.Collection 𝒮)
  (find : OrdinaryProfile.FoundationInduction 𝒮)
  (κ w : ZFStructure.S 𝒮)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import OrdinaryProfile 𝒮 using ( ChoiceSet )
open import CodedVocabulary 𝒮 using ( denseΔ )
import CardinalBridge
import K7.ChainConditions
import K8.Cohen
import K8.CohenCCC
import K8.DistinctDense
import K8.CertifiedCCCTransfer

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
module CB = CardinalBridge 𝒮 using ( isOmega )
module CH = K7.ChainConditions 𝒮 ext paths using ( CCC₂ᴵ )
module C = K8.Cohen 𝒮 ext paths pair un pow sep κ w
  using ( carrier; order; presentation; laws; D; D-dense )

module OverZFC (lem : LEM ℓ) (choice : ChoiceSet) (hw : ⟨ CB.isOmega w ⟩) where
  module CCC = K8.CohenCCC.AtOmega 𝒮 ext paths pair un pow sep coll find κ w lem choice hw
    using ( ccc )
  module Completion = K8.CertifiedCCCTransfer.AtPresentation
    𝒮 ext paths pair un pow sep coll find κ lem C.presentation C.laws w
    using ( module N; order⁺; certificate; property-transfer; property-hypotheses-inhabited
          ; certified-ccc-transfer )
  module Dense = K8.DistinctDense 𝒮 ext paths pair un pow sep find κ w hw
    using ( E; E-dense )

  cohen-ccc : ⟨ CH.CCC₂ᴵ C.carrier C.order w ⟩
  cohen-ccc = CCC.ccc

  completion-ccc : ⟨ CH.CCC₂ᴵ Completion.N.B⁺set Completion.order⁺ w ⟩
  completion-ccc = Completion.certified-ccc-transfer choice cohen-ccc

  open Completion public using ( certificate; property-transfer; property-hypotheses-inhabited )

  coordinate-dense : (α n : S) → ⟨ α ∈ˢ κ ⟩ → ⟨ n ∈ˢ w ⟩
    → ⟨ denseΔ C.carrier C.order (C.D α n) ⟩
  coordinate-dense = C.D-dense lem

  distinct-dense : (α β : S) → ⟨ α ∈ˢ κ ⟩ → ⟨ β ∈ˢ κ ⟩
    → ⟨ (α ≈ˢ β) ⇒ ⊥ ⟩ → ⟨ denseΔ C.carrier C.order (Dense.E α β) ⟩
  distinct-dense = Dense.E-dense lem

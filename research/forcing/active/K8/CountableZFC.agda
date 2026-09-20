{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile

module K8.CountableZFC
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
  (seed : ZFStructure.S 𝒮)
  where


open import FOL.ZFStructure using ( module hPropStructure )
open import Base.Classical using ( LEM )
open import CodedVocabulary 𝒮 using ( subsetΔ )
open import OrdinaryProfile 𝒮 using ( ChoiceSet )
import K8.GroundSets
import K8.CountableUnion
import K8.CountableOperations
import K8.Uncountability
import K8.DiagonalOrder
import CardinalBridge

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

module GS = K8.GroundSets.Ground 𝒮 ext paths pair un pow sep seed
module CU = K8.CountableUnion 𝒮 ext paths pair un pow sep coll find seed
module CO = K8.CountableOperations 𝒮 ext paths pair un pow sep coll find seed
module UC = K8.Uncountability 𝒮 ext paths pair un pow sep coll find seed
module CB = CardinalBridge 𝒮

module AtOmega (lem : LEM ℓ) (choice : ChoiceSet)
  (w : S) (hw : ⟨ CB.isOmega w ⟩) where
  module D = K8.DiagonalOrder.AtOmega 𝒮 ext paths pair un pow sep coll find seed lem w hw

  square : ⟨ CB.injectable (GS.product w w) w ⟩
  square = D.omega-square-injection

  countable-union : (F U : S)
    → ((a : S) → ⟨ a ∈ˢ F ⟩ → ⟨ subsetΔ a U ⟩)
    → ((u : S) → ⟨ u ∈ˢ U ⟩ → ⟨ ⋁ S (λ a → (a ∈ˢ F) ⊓ (u ∈ˢ a)) ⟩)
    → ⟨ CB.injectable F w ⟩
    → ((a : S) → ⟨ a ∈ˢ F ⟩ → ⟨ CB.injectable a w ⟩)
    → ⟨ CB.injectable U w ⟩
  countable-union F U sub cover countF each =
    CU.countable-union choice F U w sub cover countF each square

  countable-join : (a b : S) → ⟨ CB.injectable a w ⟩ → ⟨ CB.injectable b w ⟩
    → ⟨ CB.injectable (GS.join a b) w ⟩
  countable-join a b = CO.countable-join lem choice w hw square a b

  countable-bigUnion : (F : S) → ⟨ CB.injectable F w ⟩
    → ((a : S) → ⟨ a ∈ˢ F ⟩ → ⟨ CB.injectable a w ⟩)
    → ⟨ CB.injectable (CO.FU.bigUnion F) w ⟩
  countable-bigUnion F countF each = CO.countable-bigUnion choice F w countF each square

  uncountable-union-member : (F U : S)
    → ((a : S) → ⟨ a ∈ˢ F ⟩ → ⟨ subsetΔ a U ⟩)
    → ((u : S) → ⟨ u ∈ˢ U ⟩ → ⟨ ⋁ S (λ a → (a ∈ˢ F) ⊓ (u ∈ˢ a)) ⟩)
    → ⟨ CB.injectable F w ⟩ → ⟨ UC.uncountable w U ⟩
    → ⟨ ⋁ S (λ a → (a ∈ˢ F) ⊓ UC.uncountable w a) ⟩
  uncountable-union-member F U sub cover countF unU =
    UC.uncountable-union-member lem choice F U w sub cover countF square unU


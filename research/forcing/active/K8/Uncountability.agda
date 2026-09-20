{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile

module K8.Uncountability
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
open import FOL.Syntax using ( Formula )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
open import CodedVocabulary 𝒮 using ( subsetΔ )
open import OrdinaryProfile 𝒮 using ( ChoiceSet; module Swap )
import K8.GroundSets
import K8.CountableUnion
import K7.CardinalOrder
import CardinalBridge
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )

module GS = K8.GroundSets.Ground 𝒮 ext paths pair un pow sep seed
module CU = K8.CountableUnion 𝒮 ext paths pair un pow sep coll find seed
module CB = CardinalBridge 𝒮
module CO = K7.CardinalOrder.Order 𝒮 ext
  (λ x y z e → cong (_∈ˢ z) (GS.≈→≡ e))
  (λ x y z e → cong (x ∈ˢ_) (GS.≈→≡ e))

uncountable : S → S → Ω
uncountable w A = CB.injectable A w ⇒ ⊥

uncountable-upward : (w A B : S) → ⟨ subsetΔ A B ⟩
  → ⟨ uncountable w A ⟩ → ⟨ uncountable w B ⟩
uncountable-upward w A B sub unA countB = unA (CO.injectable-mono-dom A B w sub countB)

countable-image : ChoiceSet → (I F w : S) → (φ : Formula S 2)
  → ((y : S) → ⟨ y ∈ˢ F ⟩ → ⟨ ⋁ S (λ x → (x ∈ˢ I) ⊓ ((y ∷ x ∷ []) ⊨ φ)) ⟩)
  → ((x y z : S) → ⟨ x ∈ˢ I ⟩ → ⟨ y ∈ˢ F ⟩ → ⟨ z ∈ˢ F ⟩
      → ⟨ (y ∷ x ∷ []) ⊨ φ ⟩ → ⟨ (z ∷ x ∷ []) ⊨ φ ⟩ → ⟨ y ≈ˢ z ⟩)
  → ⟨ CB.injectable I w ⟩ → ⟨ CB.injectable F w ⟩
countable-image choice I F w φ onto single countI =
  CO.injectable-trans sep coll pair F I w
    (CU.choice-injection choice F I (Swap.swapFo φ)
      (λ y hy → PT.map (λ { (x , hx , sat) →
        x , hx , subst ⟨_⟩ (sym (Swap.⊨-swap φ x y)) sat }) (onto y hy))
      (λ y z x hy hz hx sy sz → single x y z hx hy hz
        (subst ⟨_⟩ (Swap.⊨-swap φ x y) sy)
        (subst ⟨_⟩ (Swap.⊨-swap φ x z) sz))) countI

uncountable-union-member : LEM ℓ → ChoiceSet → (F U w : S)
  → ((a : S) → ⟨ a ∈ˢ F ⟩ → ⟨ subsetΔ a U ⟩)
  → ((u : S) → ⟨ u ∈ˢ U ⟩ → ⟨ ⋁ S (λ a → (a ∈ˢ F) ⊓ (u ∈ˢ a)) ⟩)
  → ⟨ CB.injectable F w ⟩
  → ⟨ CB.injectable (GS.product w w) w ⟩
  → ⟨ uncountable w U ⟩
  → ⟨ ⋁ S (λ a → (a ∈ˢ F) ⊓ uncountable w a) ⟩
uncountable-union-member lem choice F U w sub cover countF square unU = decide (lem target)
  where
  target : Ω
  target = ⋁ S (λ a → (a ∈ˢ F) ⊓ uncountable w a)

  decide : ⟨ target ⟩ ⊎ (⟨ target ⟩ → Empty.⊥) → ⟨ target ⟩
  decide (inl witness) = witness
  decide (inr absent) = Empty.rec* (unU
    (CU.countable-union choice F U w sub cover countF each square))
    where
    each : (a : S) → ⟨ a ∈ˢ F ⟩ → ⟨ CB.injectable a w ⟩
    each a ha = case (lem (CB.injectable a w))
      where
      case : ⟨ CB.injectable a w ⟩ ⊎ (⟨ CB.injectable a w ⟩ → Empty.⊥)
        → ⟨ CB.injectable a w ⟩
      case (inl countA) = countA
      case (inr notA) = Empty.rec (absent ∣ a , ha , (λ c → Empty.rec (notA c)) ∣₁)


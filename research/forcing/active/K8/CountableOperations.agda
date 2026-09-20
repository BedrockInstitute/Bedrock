{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile

module K8.CountableOperations
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
import K8.FiniteOperations
import K8.FinitePairs
import K8.FiniteCountable
import K8.FiniteUnion
import K8.CountableUnion
import CardinalBridge
open import Cubical.Data.Sum using ( inl; inr )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

module GS = K8.GroundSets.Ground 𝒮 ext paths pair un pow sep seed
module FO = K8.FiniteOperations 𝒮 ext paths pair un pow sep seed
module FP = K8.FinitePairs 𝒮 ext paths pair un pow sep seed
module FC = K8.FiniteCountable 𝒮 ext paths pair un pow sep find seed
module FU = K8.FiniteUnion 𝒮 ext paths pair un pow sep seed
module CU = K8.CountableUnion 𝒮 ext paths pair un pow sep coll find seed
module CB = CardinalBridge 𝒮

countable-join : LEM ℓ → ChoiceSet → (w : S) → ⟨ CB.isOmega w ⟩
  → ⟨ CB.injectable (GS.product w w) w ⟩
  → (a b : S) → ⟨ CB.injectable a w ⟩ → ⟨ CB.injectable b w ⟩
  → ⟨ CB.injectable (GS.join a b) w ⟩
countable-join lem choice w hw square a b ca cb =
  CU.countable-union choice (GS.pairOf a b) (GS.join a b) w
    sub cover countPair each square
  where
  sub : (d : S) → ⟨ d ∈ˢ GS.pairOf a b ⟩ → ⟨ subsetΔ d (GS.join a b) ⟩
  sub d hd x hx = PT.rec (snd (x ∈ˢ GS.join a b))
    (λ { (inl eq) → FO.join-inˡ a b x (subst (λ t → ⟨ x ∈ˢ t ⟩) (GS.≈→≡ eq) hx)
       ; (inr eq) → FO.join-inʳ a b x (subst (λ t → ⟨ x ∈ˢ t ⟩) (GS.≈→≡ eq) hx) })
    (GS.pairOf-out a b d hd)

  cover : (x : S) → ⟨ x ∈ˢ GS.join a b ⟩
    → ⟨ ⋁ S (λ d → (d ∈ˢ GS.pairOf a b) ⊓ (x ∈ˢ d)) ⟩
  cover x hx = PT.map
    (λ { (inl ha) → a , GS.pairOf-inˡ a b , ha
       ; (inr hb) → b , GS.pairOf-inʳ a b , hb })
    (subst ⟨_⟩ (GS.join-spec a b x) hx)

  countPair : ⟨ CB.injectable (GS.pairOf a b) w ⟩
  countPair = FC.finite-countable lem w hw (GS.pairOf a b) (GS.pairOf a b)
    (FP.finite-pair (GS.pairOf a b) a b (GS.pairOf-inˡ a b) (GS.pairOf-inʳ a b))

  each : (d : S) → ⟨ d ∈ˢ GS.pairOf a b ⟩ → ⟨ CB.injectable d w ⟩
  each d hd = PT.rec (snd (CB.injectable d w))
    (λ { (inl eq) → subst (λ t → ⟨ CB.injectable t w ⟩) (sym (GS.≈→≡ eq)) ca
       ; (inr eq) → subst (λ t → ⟨ CB.injectable t w ⟩) (sym (GS.≈→≡ eq)) cb })
    (GS.pairOf-out a b d hd)

countable-bigUnion : ChoiceSet → (F w : S)
  → ⟨ CB.injectable F w ⟩
  → ((a : S) → ⟨ a ∈ˢ F ⟩ → ⟨ CB.injectable a w ⟩)
  → ⟨ CB.injectable (GS.product w w) w ⟩
  → ⟨ CB.injectable (FU.bigUnion F) w ⟩
countable-bigUnion choice F w cf each square =
  CU.countable-union choice F (FU.bigUnion F) w
    (λ a ha x hx → subst ⟨_⟩ (sym (FU.bigUnion-spec F x)) ∣ a , ha , hx ∣₁)
    (λ x hx → subst ⟨_⟩ (FU.bigUnion-spec F x) hx)
    cf each square


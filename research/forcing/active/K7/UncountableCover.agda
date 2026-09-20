{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile

module K7.UncountableCover
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
  (choice : OrdinaryProfile.ChoiceSet 𝒮)
  (w : ZFStructure.S 𝒮)
  where

open import FOL.ZFStructure using ( module hPropStructure )
import CardinalBridge
import K7.CardinalOrder
import K8.CountableUnion
import K8.FiniteUnion
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

module CB = CardinalBridge 𝒮
module CU = K8.CountableUnion 𝒮 ext paths pair un pow sep coll find w
module FU = K8.FiniteUnion 𝒮 ext paths pair un pow sep w
module CO = K7.CardinalOrder.Order 𝒮 ext
  (λ x y z e → cong (_∈ˢ z) (subst ⟨_⟩ (paths x y) e))
  (λ x y z e → cong (x ∈ˢ_) (subst ⟨_⟩ (paths y z) e))

union-bound : (F d : S)
  → ⟨ CB.injectable F d ⟩
  → ((v : S) → ⟨ v ∈ˢ F ⟩ → ⟨ CB.injectable v w ⟩)
  → ⟨ CB.injectable w d ⟩
  → ⟨ CB.injectable (CU.GS.product d d) d ⟩
  → ⟨ CB.injectable (FU.bigUnion F) d ⟩
union-bound F d hF each wd square = CU.countable-union choice F
  (FU.bigUnion F) d
  (λ v hv a ha → subst ⟨_⟩ (sym (FU.bigUnion-spec F a))
    ∣ v , hv , ha ∣₁)
  (λ a ha → subst ⟨_⟩ (FU.bigUnion-spec F a) ha)
  hF (λ v hv → CO.injectable-trans sep coll pair v w d (each v hv) wd) square

ProvedRange : S → Ω
ProvedRange κ = ⋀ S (λ β → (β ∈ˢ κ) ⇒ ⋀ S (λ F →
  (CB.injectable F β ⊓
    ((⋀ S (λ v → (v ∈ˢ F) ⇒ CB.injectable v w)) ⊓
    (⋀ S (λ a → (a ∈ˢ κ) ⇒ ⋁ S (λ v → (v ∈ˢ F) ⊓ (a ∈ˢ v)))))) ⇒ ⊥))

proved-range : (d κ : S)
  → ⟨ CB.isCardinal κ ⟩ → ⟨ d ∈ˢ κ ⟩
  → ⟨ CB.injectable w d ⟩
  → ((β : S) → ⟨ β ∈ˢ κ ⟩ → ⟨ CB.injectable β d ⟩)
  → ⟨ CB.injectable (CU.GS.product d d) d ⟩
  → ⟨ ProvedRange κ ⟩
proved-range d κ cardκ hd wd below square β hβ F (hF , each , cover) =
  lift (cardκ .snd d hd (CO.injectable-trans sep coll pair κ
    (FU.bigUnion F) d
    (CO.injectable-incl sep coll pair κ (FU.bigUnion F)
      (λ a ha → subst ⟨_⟩ (sym (FU.bigUnion-spec F a)) (cover a ha)))
    (union-bound F d (CO.injectable-trans sep coll pair F β d hF (below β hβ))
      each wd square)))

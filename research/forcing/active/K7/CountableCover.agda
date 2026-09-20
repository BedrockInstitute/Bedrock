{-# OPTIONS --cubical --safe --guardedness #-}

-- A countable-cover obstruction for a ground cardinal. If every member of κ
-- injects into ω, then no family indexed by a member of κ and consisting of
-- ω-countable sets covers κ. The family members need not be subsets of κ:
-- the proof counts their full union and only then embeds κ into that union.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile
import CardinalBridge
import K7.CardinalOrder
import K8.CountableZFC

module K7.CountableCover
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext   : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
         → ZFStructure._≈ˢ_ 𝒮 x y
           ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  (pair  : OrdinaryProfile.Pairing 𝒮)
  (un    : OrdinaryProfile.Union 𝒮)
  (pow   : OrdinaryProfile.PowerSet 𝒮)
  (sep   : OrdinaryProfile.Separation 𝒮)
  (coll  : OrdinaryProfile.Collection 𝒮)
  (find  : OrdinaryProfile.FoundationInduction 𝒮)
  (lem   : LEM ℓ)
  (choice : OrdinaryProfile.ChoiceSet 𝒮)
  (w     : ZFStructure.S 𝒮)
  (hw    : ⟨ CardinalBridge.isOmega 𝒮 w ⟩)
  (κ     : ZFStructure.S 𝒮)
  (cardκ : ⟨ CardinalBridge.isCardinal 𝒮 κ ⟩)
  (w∈κ   : ⟨ ZFStructure._∈ˢ_ 𝒮 w κ ⟩)
  (members-countable : (β : ZFStructure.S 𝒮)
                     → ⟨ ZFStructure._∈ˢ_ 𝒮 β κ ⟩
                     → ⟨ CardinalBridge.injectable 𝒮 β w ⟩)
  where

open import FOL.ZFStructure using ( module hPropStructure )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

module CB = CardinalBridge 𝒮
module CO = K7.CardinalOrder.Order 𝒮 ext
  (λ x y z e → cong (_∈ˢ z) (subst ⟨_⟩ (paths x y) e))
  (λ x y z e → cong (x ∈ˢ_) (subst ⟨_⟩ (paths y z) e))
module ZFC = K8.CountableZFC 𝒮 ext paths pair un pow sep coll find w
module CZ = ZFC.AtOmega lem choice w hw

-- This is definitionally the formula called ProvedRange w by
-- K7.NoCollapse: no β below κ indexes a family of w-countable sets covering κ.

ProvedRange : Ω
ProvedRange =
  ⋀ S (λ β → (β ∈ˢ κ) ⇒
  ⋀ S (λ F →
       (  (CB.injectable F β)
        ⊓ ((⋀ S (λ v → (v ∈ˢ F) ⇒ CB.injectable v w))
        ⊓ (⋀ S (λ a → (a ∈ˢ κ) ⇒
             ⋁ S (λ v → (v ∈ˢ F) ⊓ (a ∈ˢ v))))))
     ⇒ ⊥))

proved-range : ⟨ ProvedRange ⟩
proved-range β hβ F (hFβ , hEach , hCover) =
  lift (cardκ .snd w w∈κ κ-countable)
  where
    F-countable : ⟨ CB.injectable F w ⟩
    F-countable = CO.injectable-trans sep coll pair F β w hFβ
      (members-countable β hβ)

    union-countable : ⟨ CB.injectable (ZFC.CO.FU.bigUnion F) w ⟩
    union-countable = CZ.countable-bigUnion F F-countable hEach

    κ-subset-union : ⟨ CB.isSubset κ (ZFC.CO.FU.bigUnion F) ⟩
    κ-subset-union a ha =
      subst ⟨_⟩ (sym (ZFC.CO.FU.bigUnion-spec F a)) (hCover a ha)

    κ-injects-union : ⟨ CB.injectable κ (ZFC.CO.FU.bigUnion F) ⟩
    κ-injects-union =
      CO.injectable-incl sep coll pair κ (ZFC.CO.FU.bigUnion F) κ-subset-union

    κ-countable : ⟨ CB.injectable κ w ⟩
    κ-countable = CO.injectable-trans sep coll pair κ
      (ZFC.CO.FU.bigUnion F) w κ-injects-union union-countable

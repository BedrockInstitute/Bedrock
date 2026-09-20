{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile

module K8.FiniteProduct
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
    → ZFStructure._≈ˢ_ 𝒮 x y ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  (pair : OrdinaryProfile.Pairing 𝒮)
  (un : OrdinaryProfile.Union 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (sep : OrdinaryProfile.Separation 𝒮)
  (seed : ZFStructure.S 𝒮)
  where


open import FOL.ZFStructure using ( module hPropStructure )
open import Base.Classical using ( LEM )
open import CodedVocabulary 𝒮 using ( subsetΔ; isKPairΔ )
open import K8.FiniteVocabulary 𝒮 using ( finiteIn )
open import K8.FiniteSubsets 𝒮 ext paths pow sep using ( finite-subset )
open import K8.FiniteAmbient 𝒮 ext paths pow sep using ( finite-change-ambient )
import K8.GroundSets
import K8.FiniteOperations
import K8.FinitePower
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

module GS = K8.GroundSets.Ground 𝒮 ext paths pair un pow sep seed
module FO = K8.FiniteOperations 𝒮 ext paths pair un pow sep seed
module FP = K8.FinitePower 𝒮 ext paths pair un pow sep seed

pair-subset : (A x y : S) → ⟨ x ∈ˢ A ⟩ → ⟨ y ∈ˢ A ⟩
  → ⟨ subsetΔ (GS.pairOf x y) A ⟩
pair-subset A x y hx hy z hz = PT.rec (snd (z ∈ˢ A))
  (λ { (inl eq) → subst (λ t → ⟨ t ∈ˢ A ⟩) (sym (GS.≈→≡ eq)) hx
     ; (inr eq) → subst (λ t → ⟨ t ∈ˢ A ⟩) (sym (GS.≈→≡ eq)) hy })
  (GS.pairOf-out x y z hz)

ordered-bound : (a b x y : S) → ⟨ x ∈ˢ a ⟩ → ⟨ y ∈ˢ b ⟩
  → ⟨ GS.ordered x y ∈ˢ GS.power (GS.power (GS.join a b)) ⟩
ordered-bound a b x y hx hy =
  subst ⟨_⟩ (sym (GS.power-spec (GS.power (GS.join a b)) (GS.ordered x y)))
    (pair-subset (GS.power (GS.join a b)) (GS.singleton x) (GS.pairOf x y)
      (subst ⟨_⟩ (sym (GS.power-spec (GS.join a b) (GS.singleton x)))
        (pair-subset (GS.join a b) x x (FO.join-inˡ a b x hx) (FO.join-inˡ a b x hx)))
      (subst ⟨_⟩ (sym (GS.power-spec (GS.join a b) (GS.pairOf x y)))
        (pair-subset (GS.join a b) x y (FO.join-inˡ a b x hx) (FO.join-inʳ a b y hy))))

product-bound : (a b : S)
  → ⟨ subsetΔ (GS.product a b) (GS.power (GS.power (GS.join a b))) ⟩
product-bound a b z hz = PT.rec (snd (z ∈ˢ GS.power (GS.power (GS.join a b))))
  (λ { (x , y , hx , hy , kp) →
    subst (λ t → ⟨ t ∈ˢ GS.power (GS.power (GS.join a b)) ⟩)
      (sym (GS.ordered-unique z x y kp)) (ordered-bound a b x y hx hy) })
  (GS.product-out a b z hz)

product-mono : (a b X Y : S) → ⟨ subsetΔ a X ⟩ → ⟨ subsetΔ b Y ⟩
  → ⟨ subsetΔ (GS.product a b) (GS.product X Y) ⟩
product-mono a b X Y as bs z hz = PT.rec (snd (z ∈ˢ GS.product X Y))
  (λ { (x , y , hx , hy , kp) → subst (λ t → ⟨ t ∈ˢ GS.product X Y ⟩)
    (sym (GS.ordered-unique z x y kp)) (GS.product-in X Y x y (as x hx) (bs y hy)) })
  (GS.product-out a b z hz)

finite-product : LEM ℓ → (X Y a b : S)
  → ⟨ finiteIn X a ⟩ → ⟨ finiteIn Y b ⟩
  → ⟨ finiteIn (GS.product X Y) (GS.product a b) ⟩
finite-product lem X Y a b ha hb =
  finite-change-ambient (GS.power (GS.power Z)) (GS.product X Y) (GS.product a b)
    (finite-subset lem (GS.power (GS.power Z))
      (GS.power (GS.power (GS.join a b))) (GS.product a b) twice (product-bound a b))
    (product-mono a b X Y (fst ha) (fst hb))
  where
  Z : S
  Z = GS.join X Y

  joined : ⟨ finiteIn Z (GS.join a b) ⟩
  joined = FO.finite-join Z a b
    (finite-change-ambient X Z a ha (λ x hx → FO.join-inˡ X Y x (fst ha x hx)))
    (finite-change-ambient Y Z b hb (λ y hy → FO.join-inʳ X Y y (fst hb y hy)))

  once : ⟨ finiteIn (GS.power Z) (GS.power (GS.join a b)) ⟩
  once = FP.powerset-finite Z lem (GS.join a b) joined

  twice : ⟨ finiteIn (GS.power (GS.power Z)) (GS.power (GS.power (GS.join a b))) ⟩
  twice = FP.powerset-finite (GS.power Z) lem (GS.power (GS.join a b)) once


{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile

module K8.FinitePairs
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
open import K8.FiniteVocabulary 𝒮 using ( finiteIn; adjoinPred )
open import K8.FiniteSets 𝒮 ext paths pow sep using ( finite-empty; finite-adjoin )
import K8.GroundSets
open import Cubical.Data.Sum using ( inl; inr )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )
import Cubical.Data.Empty as Empty

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

module GS = K8.GroundSets.Ground 𝒮 ext paths pair un pow sep seed

finite-singleton : (X x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ finiteIn X (GS.singleton x) ⟩
finite-singleton X x hx = finite-adjoin X (GS.singleton x) GS.empty x
  (finite-empty X GS.empty GS.empty-out) hx
  (fst (GS.singleton-witness x) ,
    (λ z hz → Empty.rec* (GS.empty-out z hz)) ,
    (λ z hz → ∣ inr (snd (GS.singleton-witness x) z hz) ∣₁))

finite-pair : (X x y : S) → ⟨ x ∈ˢ X ⟩ → ⟨ y ∈ˢ X ⟩
  → ⟨ finiteIn X (GS.pairOf x y) ⟩
finite-pair X x y hx hy =
  finite-adjoin X (GS.pairOf x y) (GS.singleton x) y (finite-singleton X x hx) hy ad
  where
  ad : ⟨ adjoinPred (GS.pairOf x y) (GS.singleton x) y ⟩
  ad = GS.pairOf-inʳ x y ,
    (λ z hz → subst (λ t → ⟨ t ∈ˢ GS.pairOf x y ⟩)
      (sym (GS.≈→≡ (snd (GS.singleton-witness x) z hz))) (GS.pairOf-inˡ x y)) ,
    (λ z hz → PT.map
      (λ { (inl eq) → inl (subst (λ t → ⟨ t ∈ˢ GS.singleton x ⟩)
          (sym (GS.≈→≡ eq)) (fst (GS.singleton-witness x)))
         ; (inr eq) → inr eq }) (GS.pairOf-out x y z hz))


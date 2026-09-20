{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile

module K8.CohenFibers
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
    → ZFStructure._≈ˢ_ 𝒮 x y ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  (pair : OrdinaryProfile.Pairing 𝒮)
  (un : OrdinaryProfile.Union 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (sep : OrdinaryProfile.Separation 𝒮)
  (κ w : ZFStructure.S 𝒮)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import Base.Classical using ( LEM )
open import CodedVocabulary 𝒮 using ( subsetΔ )
open import K8.FiniteVocabulary 𝒮 using ( finiteIn; adjoinPred )
open import K8.FiniteSets 𝒮 ext paths pow sep using ( finite-empty; finite-adjoin )
import K8.Cohen
import K8.FiniteFibers
import K8.DomainFinite
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )
import Cubical.Data.Empty as Empty

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

module C = K8.Cohen 𝒮 ext paths pair un pow sep κ w
module GS = C.GS
module PM = C.PM
module F = K8.FiniteFibers 𝒮 ext paths pair un pow sep κ C.coordinates C.two
module DF = K8.DomainFinite 𝒮 ext paths pair un pow sep κ C.coordinates C.two

bit₁-finite : ⟨ finiteIn C.two C.bit₁ ⟩
bit₁-finite = finite-adjoin C.two C.bit₁ C.bit₀ C.bit₀
  (finite-empty C.two C.bit₀ GS.empty-out) C.bit₀-in
  (fst (GS.singleton-witness C.bit₀) ,
    (λ z hz → Empty.rec* (GS.empty-out z hz)) ,
    (λ z hz → ∣ inr (snd (GS.singleton-witness C.bit₀) z hz) ∣₁))

two-finite : ⟨ finiteIn C.two C.two ⟩
two-finite = finite-adjoin C.two C.two C.bit₁ C.bit₁ bit₁-finite C.bit₁-in ad
  where
  ad : ⟨ adjoinPred C.two C.bit₁ C.bit₁ ⟩
  ad = C.bit₁-in ,
    (λ z hz → subst (λ t → ⟨ t ∈ˢ C.two ⟩)
      (sym (GS.≈→≡ (snd (GS.singleton-witness C.bit₀) z hz))) C.bit₀-in) ,
    (λ z hz → PT.map
      (λ { (inl eq) → inl (subst (λ t → ⟨ t ∈ˢ C.bit₁ ⟩)
          (sym (GS.≈→≡ eq)) (fst (GS.singleton-witness C.bit₀)))
         ; (inr eq) → inr eq }) (GS.pairOf-out C.bit₀ C.bit₁ z hz))

conditions-on-domain-finite : LEM ℓ → (p : S) → ⟨ p ∈ˢ C.carrier ⟩
  → ⟨ finiteIn C.carrier (F.fiber (PM.domain p)) ⟩
conditions-on-domain-finite lem p hp = F.finite-fiber lem (PM.domain p)
  (DF.domain-finite p (fst (subst ⟨_⟩ (PM.carrier-spec p) hp))) two-finite

same-domain-in-fiber : (p q : S) → ⟨ q ∈ˢ C.carrier ⟩
  → ⟨ PM.domain q ≈ˢ PM.domain p ⟩
  → ⟨ q ∈ˢ F.fiber (PM.domain p) ⟩
same-domain-in-fiber p q hq eq = F.fiber-in (PM.domain p) q hq
  (λ x hx → subst (λ t → ⟨ x ∈ˢ t ⟩) (GS.≈→≡ eq) hx)


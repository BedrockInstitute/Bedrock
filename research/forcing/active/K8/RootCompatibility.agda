{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile

module K8.RootCompatibility
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
    → ZFStructure._≈ˢ_ 𝒮 x y ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  (pair : OrdinaryProfile.Pairing 𝒮)
  (un : OrdinaryProfile.Union 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (sep : OrdinaryProfile.Separation 𝒮)
  (seed X Y : ZFStructure.S 𝒮)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import CodedVocabulary 𝒮 using ( refinesΔ; compatibleΔ )
open import K8.MapVocabulary 𝒮 using ( agrees )
import K8.GroundSets
import K8.PartialMaps
import K8.MapOperations
import K8.Restriction
import K7.ChainConditions

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

module GS = K8.GroundSets.Ground 𝒮 ext paths pair un pow sep seed
module PM = K8.PartialMaps.Maps 𝒮 ext paths pair un pow sep seed X Y
module MO = K8.MapOperations.Operations 𝒮 ext paths pair un pow sep seed X Y
module R = K8.Restriction 𝒮 ext paths pair un pow sep seed X Y
module CC = K7.ChainConditions 𝒮 ext paths

overlap-in-root : S → S → S → Ω
overlap-in-root p q r = ⋀ S (λ x →
  ((x ∈ˢ PM.domain p) ⊓ (x ∈ˢ PM.domain q)) ⇒ (x ∈ˢ r))

root-agreement : (p q r : S) → ⟨ q ∈ˢ PM.carrier ⟩
  → ⟨ overlap-in-root p q r ⟩
  → ⟨ R.restrict p r ≈ˢ R.restrict q r ⟩
  → ⟨ agrees X Y p q ⟩
root-agreement p q r hq covered equal x hx y hy z hz values =
  snd (subst ⟨_⟩ (PM.carrier-spec q) hq) x hx y hy z hz
    (fst (R.lookup-restrict-out q r x y onQ) , snd values)
  where
  inRoot : ⟨ x ∈ˢ r ⟩
  inRoot = covered x
    (PM.domain-in p x y hx hy (fst values) ,
     PM.domain-in q x z hx hz (snd values))

  onP : ⟨ refinesΔ (R.restrict p r) x y ⟩
  onP = R.lookup-restrict-in p r x y hy (fst values) inRoot

  onQ : ⟨ refinesΔ (R.restrict q r) x y ⟩
  onQ = subst (λ t → ⟨ refinesΔ t x y ⟩) (GS.≈→≡ equal) onP

root-compatible : (p q r : S)
  → ⟨ p ∈ˢ PM.carrier ⟩ → ⟨ q ∈ˢ PM.carrier ⟩
  → ⟨ overlap-in-root p q r ⟩
  → ⟨ R.restrict p r ≈ˢ R.restrict q r ⟩
  → ⟨ compatibleΔ PM.carrier MO.CP.order p q ⟩
root-compatible p q r hp hq covered equal =
  MO.agrees→compatible p q hp hq (root-agreement p q r hq covered equal)

antichain-root-injective : (d p q r : S)
  → ⟨ CC.antichainΔ PM.carrier MO.CP.order d ⟩
  → ⟨ p ∈ˢ PM.carrier ⟩ → ⟨ p ∈ˢ d ⟩
  → ⟨ q ∈ˢ PM.carrier ⟩ → ⟨ q ∈ˢ d ⟩
  → ⟨ overlap-in-root p q r ⟩
  → ⟨ R.restrict p r ≈ˢ R.restrict q r ⟩
  → ⟨ p ≈ˢ q ⟩
antichain-root-injective d p q r hd hp hpd hq hqd covered equal =
  CC.antichain-use PM.carrier MO.CP.order d p q hd hp hpd hq hqd
    (root-compatible p q r hp hq covered equal)

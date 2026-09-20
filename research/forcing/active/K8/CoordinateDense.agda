{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile

module K8.CoordinateDense
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
open import FOL.Syntax using ( Formula )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
open import Base.Classical using ( LEM )
open import CodedVocabulary 𝒮 using ( denseΔ; refinesΔ; sepAt; sepAt-reading )
open import K8.MapVocabulary 𝒮 using ( domainAt; domainPred )
import K8.GroundSets
import K8.PartialMaps
import K8.Presentation
import K8.MapOperations
module GS = K8.GroundSets.Ground 𝒮 ext paths pair un pow sep seed
module PM = K8.PartialMaps.Maps 𝒮 ext paths pair un pow sep seed X Y
module PC = K8.Presentation.CohenPresentation 𝒮 ext paths pair un pow sep seed X Y
module MO = K8.MapOperations.Operations 𝒮 ext paths pair un pow sep seed X Y
open import Cubical.Data.Sum using ( _⊎_ ) renaming ( inl to inl⊎; inr to inr⊎ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )
import Cubical.Data.Empty as Empty

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )

coordinateFormula : S → Formula S 1
coordinateFormula x = sepAt (domainAt (suc zero) zero (suc (suc zero))) (Y ∷ x ∷ [])

coordinate-reading : (x p : S)
  → ((p ∷ []) ⊨ coordinateFormula x) ≡ domainPred Y p x
coordinate-reading x p = sepAt-reading
  (domainAt (suc zero) zero (suc (suc zero))) (Y ∷ x ∷ []) p

opaque
  D : S → S
  D x = GS.separator PM.carrier (coordinateFormula x)

  D-spec : (x p : S)
    → (p ∈ˢ D x) ≡ ((p ∈ˢ PM.carrier) ⊓ domainPred Y p x)
  D-spec x p = GS.separator-spec PM.carrier (coordinateFormula x) p
    ∙ cong ((p ∈ˢ PM.carrier) ⊓_) (coordinate-reading x p)

coordinate-dense : LEM ℓ → (x y : S) → ⟨ x ∈ˢ X ⟩ → ⟨ y ∈ˢ Y ⟩
  → ⟨ denseΔ PM.carrier PC.order (D x) ⟩
coordinate-dense lem x y hx hy p hp = choose (lem (x ∈ˢ PM.domain p))
  where
  choose : ⟨ x ∈ˢ PM.domain p ⟩ ⊎ (⟨ x ∈ˢ PM.domain p ⟩ → Empty.⊥)
    → ⟨ ⋁ S (λ q → (q ∈ˢ D x) ⊓ refinesΔ PC.order q p) ⟩
  choose (inl⊎ defined) = ∣ p , subst ⟨_⟩ (sym (D-spec x p))
    (hp , snd (subst ⟨_⟩ (PM.domain-spec p x) defined))
    , subst ⟨_⟩ (sym (PC.refines-spec p p hp hp)) (λ z hz → hz) ∣₁
  choose (inr⊎ fresh) = ∣ q , subst ⟨_⟩ (sym (D-spec x q))
    (hq , ∣ y , hy , MO.insert-evaluates p x y ∣₁)
    , subst ⟨_⟩ (sym (PC.refines-spec q p hq hp)) (MO.insert-extends p x y) ∣₁
    where
    q : S
    q = MO.insert p x y

    hq : ⟨ q ∈ˢ PM.carrier ⟩
    hq = MO.insert-in-carrier p x y hp hx hy (λ h → Empty.rec (fresh h))

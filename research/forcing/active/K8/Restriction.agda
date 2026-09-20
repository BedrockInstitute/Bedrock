{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile

module K8.Restriction
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
open import FOL.Syntax using ( Formula; var; con; ∃̇∈ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
open import Base.Classical using ( LEM )
open import CodedVocabulary 𝒮 using ( subsetΔ; isKPairΔ; refinesΔ; prAtˢ )
open import K8.FiniteSubsets 𝒮 ext paths pow sep using ( finite-subset )
open import K8.MapVocabulary 𝒮 using ( functional )
import K8.GroundSets
import K8.PartialMaps
module GS = K8.GroundSets.Ground 𝒮 ext paths pair un pow sep seed
module PM = K8.PartialMaps.Maps 𝒮 ext paths pair un pow sep seed X Y
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )

restrictionFormula : S → Formula S 1
restrictionFormula A = ∃̇∈ (con A) (∃̇∈ (con Y)
  (prAtˢ (suc (suc zero)) (suc zero) zero))

opaque
  restrict : S → S → S
  restrict p A = GS.separator p (restrictionFormula A)

  restrict-spec : (p A e : S)
    → (e ∈ˢ restrict p A) ≡ ((e ∈ˢ p) ⊓
      (⋁ S (λ x → (x ∈ˢ A) ⊓ ⋁ S (λ y → (y ∈ˢ Y) ⊓ isKPairΔ e x y))))
  restrict-spec p A e = GS.separator-spec p (restrictionFormula A) e

restrict-subset : (p A : S) → ⟨ subsetΔ (restrict p A) p ⟩
restrict-subset p A e he = fst (subst ⟨_⟩ (restrict-spec p A e) he)

lookup-restrict-out : (p A x y : S) → ⟨ refinesΔ (restrict p A) x y ⟩
  → ⟨ (refinesΔ p x y) ⊓ (x ∈ˢ A) ⟩
lookup-restrict-out p A x y = PT.rec (snd ((refinesΔ p x y) ⊓ (x ∈ˢ A)))
  (λ { (e , he , hp) → ∣ e , restrict-subset p A e he , hp ∣₁ , inA e he hp })
  where
  inA : (e : S) → ⟨ e ∈ˢ restrict p A ⟩ → ⟨ isKPairΔ e x y ⟩ → ⟨ x ∈ˢ A ⟩
  inA e he hp = PT.rec (snd (x ∈ˢ A))
    (λ { (x' , hx' , rest) → PT.rec (snd (x ∈ˢ A))
      (λ { (y' , hy' , hp') → subst (λ z → ⟨ z ∈ˢ A ⟩)
        (sym (fst (GS.ordered-components e x y x' y' hp hp'))) hx' }) rest })
    (snd (subst ⟨_⟩ (restrict-spec p A e) he))

lookup-restrict-in : (p A x y : S) → ⟨ y ∈ˢ Y ⟩
  → ⟨ refinesΔ p x y ⟩ → ⟨ x ∈ˢ A ⟩ → ⟨ refinesΔ (restrict p A) x y ⟩
lookup-restrict-in p A x y hy old hx = PT.map
  (λ { (e , he , hp) → e , subst ⟨_⟩ (sym (restrict-spec p A e))
    (he , ∣ x , hx , ∣ y , hy , hp ∣₁ ∣₁) , hp }) old

lookup-restrict : (p A x y : S) → ⟨ y ∈ˢ Y ⟩
  → refinesΔ (restrict p A) x y ≡ ((refinesΔ p x y) ⊓ (x ∈ˢ A))
lookup-restrict p A x y hy = ⇔toPath (lookup-restrict-out p A x y)
  (λ h → lookup-restrict-in p A x y hy (fst h) (snd h))

restrict-in-carrier : LEM ℓ → (p A : S) → ⟨ p ∈ˢ PM.carrier ⟩
  → ⟨ restrict p A ∈ˢ PM.carrier ⟩
restrict-in-carrier lem p A hp = subst ⟨_⟩ (sym (PM.carrier-spec (restrict p A)))
  ( finite-subset lem PM.W p (restrict p A) (fst data') (restrict-subset p A)
  , (λ x hx y hy z hz h → snd data' x hx y hy z hz
      (fst (lookup-restrict-out p A x y (fst h))
      , fst (lookup-restrict-out p A x z (snd h)))) )
  where
  data' = subst ⟨_⟩ (PM.carrier-spec p) hp

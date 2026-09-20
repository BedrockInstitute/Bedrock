{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )

module K8.PartialMaps {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
open import OrdinaryProfile 𝒮 using
  ( Extensionality; Pairing; Union; PowerSet; Separation )
open import CodedVocabulary 𝒮 using ( refinesΔ; sepAt; sepAt-reading )
open import K8.FiniteVocabulary 𝒮 using ( finiteIn; emptyPred )
import K8.MapVocabulary
open import K8.MapVocabulary 𝒮 using
  ( functional; functionalAt; domainPred; domainAt )
import K8.GroundSets
import K8.FiniteSets
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )

module Maps
  (ext   : Extensionality)
  (paths : (x y : S) → (x ≈ˢ y) ≡ ((x ≡ y) , isSetS x y))
  (pair  : Pairing)
  (un    : Union)
  (pow   : PowerSet)
  (sep   : Separation)
  (seed  : S)
  (X Y   : S) where

  module GS = K8.GroundSets.Ground 𝒮 ext paths pair un pow sep seed
  module FS = K8.FiniteSets 𝒮 ext paths pow sep
  module MV = K8.MapVocabulary 𝒮

  W : S
  W = GS.product X Y

  functionalFormula : Formula S 1
  functionalFormula = sepAt
    (functionalAt (suc (suc zero)) (suc zero) zero) (Y ∷ X ∷ [])

  functionalFormula-reading : (f : S)
    → ((f ∷ []) ⊨ functionalFormula) ≡ functional X Y f
  functionalFormula-reading f =
    sepAt-reading (functionalAt (suc (suc zero)) (suc zero) zero)
      (Y ∷ X ∷ []) f
    ∙ MV.functional-reading
        (suc (suc zero)) (suc zero) zero (f ∷ Y ∷ X ∷ [])

  opaque
    carrier : S
    carrier = GS.separator (FS.finiteSubsets W) functionalFormula

    carrier-spec : (f : S)
      → (f ∈ˢ carrier) ≡ (finiteIn W f ⊓ functional X Y f)
    carrier-spec f =
      GS.separator-spec (FS.finiteSubsets W) functionalFormula f
      ∙ cong₂ _⊓_ (FS.finiteSubsets-spec W f) (functionalFormula-reading f)

  empty-functional : ⟨ functional X Y GS.empty ⟩
  empty-functional x hx y hy z hz h =
    PT.rec (snd (y ≈ˢ z))
      (λ { (p , hp , _) → Empty.rec* (GS.empty-out p hp) })
      (h .fst)

  empty-in-carrier : ⟨ GS.empty ∈ˢ carrier ⟩
  empty-in-carrier = subst ⟨_⟩ (sym (carrier-spec GS.empty))
    (FS.finite-empty W GS.empty (λ z hz → GS.empty-out z hz) , empty-functional)

  domainFormula : (f : S) → Formula S 1
  domainFormula f = sepAt (domainAt (suc (suc zero)) (suc zero) zero)
    (f ∷ Y ∷ [])

  domainFormula-reading : (f x : S)
    → ((x ∷ []) ⊨ domainFormula f) ≡ domainPred Y f x
  domainFormula-reading f x =
    sepAt-reading (domainAt (suc (suc zero)) (suc zero) zero) (f ∷ Y ∷ []) x
    ∙ MV.domain-reading
        (suc (suc zero)) (suc zero) zero (x ∷ f ∷ Y ∷ [])

  opaque
    domain : S → S
    domain f = GS.separator X (domainFormula f)

    domain-spec : (f x : S)
      → (x ∈ˢ domain f) ≡ ((x ∈ˢ X) ⊓ domainPred Y f x)
    domain-spec f x = GS.separator-spec X (domainFormula f) x
      ∙ cong ((x ∈ˢ X) ⊓_) (domainFormula-reading f x)

  domain-in : (f x y : S) → ⟨ x ∈ˢ X ⟩ → ⟨ y ∈ˢ Y ⟩
            → ⟨ refinesΔ f x y ⟩ → ⟨ x ∈ˢ domain f ⟩
  domain-in f x y hx hy h = subst ⟨_⟩ (sym (domain-spec f x))
    (hx , ∣ y , hy , h ∣₁)

  support : S → S
  support = domain

  support-spec : (f x : S)
    → (x ∈ˢ support f) ≡ ((x ∈ˢ X) ⊓ domainPred Y f x)
  support-spec = domain-spec

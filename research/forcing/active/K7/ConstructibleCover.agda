{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import L.Constructible using ( 𝒮ʟ )
import OrdinaryProfile

module K7.ConstructibleCover {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
  (find : OrdinaryProfile.FoundationInduction (𝒮ʟ {ℓ}))
  (choice : OrdinaryProfile.ChoiceSet (𝒮ʟ {ℓ}))
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import L.Constructible {ℓ} using ( IsOrd )
open import L.Axioms.Infinity {ℓ} lem using ( ωʟ )
open import L.Coding.Model {ℓ} using ( appC; appC-adequate; domAt-in; prAtL-adequate )
open import L.Coding.Injection {ℓ} lem using ( injAt-out )
open import L.Cardinal {ℓ} lem using ( InjCode; InjL; IsCardinalL )
open import L.GCH.CardinalSquareLaw {ℓ} lem using ( prodL; prodL-in; square-law-L )
open import V.Coding {ℓ} using ( pr )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
open import LInstanceCore {ℓ}
  using ( extensionalityL; ≈ˢ-pathsL; pairingL; unionL )
open import LInstanceSets {ℓ} lem using ( powerL; separationL )
open import LInstanceFamilies {ℓ} lem using ( replacementL )
import Cubical.HITs.PropositionalTruncation as PT
import CardinalBridge
import K7.UncountableCover

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure (𝒮ʟ {ℓ})

module CB = CardinalBridge (𝒮ʟ {ℓ})
module UC = K7.UncountableCover (𝒮ʟ {ℓ}) extensionalityL ≈ˢ-pathsL
  pairingL unionL powerL separationL replacementL find choice ωʟ
module CU = UC.CU
module CO = UC.CO
module GS = CU.GS

coded-injection : (A B : S) → InjL A B → ⟨ CB.injectable A B ⟩
coded-injection A B = PT.rec (snd (CB.injectable A B)) build
  where
  build : Σ[ F ∈ S ] InjCode F A B → ⟨ CB.injectable A B ⟩
  build (F , sv , dm , ij , ran) = CU.choice-injection choice A B
    (appC F (suc zero) zero)
    (λ x hx → PT.map (λ { (y , h) → y , ran x y h ,
      subst ⟨_⟩ (sym (appC-adequate F (suc zero) zero (y ∷ x ∷ []))) h })
      (domAt-in zero (suc zero) (F ∷ A ∷ []) dm x hx))
    (λ x z y _ _ _ h k → injAt-out zero (F ∷ A ∷ []) ij y x z
      (subst ⟨_⟩ (appC-adequate F (suc zero) zero (y ∷ x ∷ [])) h)
      (subst ⟨_⟩ (appC-adequate F (suc zero) zero (y ∷ z ∷ [])) k))

cardinal-internal : (d : S) → ⟨ CB.isCardinal d ⟩ → IsCardinalL d
cardinal-internal d hd β hβ inj = hd .snd β hβ (coded-injection d β inj)

ordered-reading : (p a b : S) → ⟨ CU.CV.isKPairΔ p a b ⟩
  → fst p ≡ pr (fst a) (fst b)
ordered-reading p a b h = subst ⟨_⟩
  (prAtL-adequate zero (suc zero) (suc (suc zero)) (p ∷ a ∷ b ∷ [])) h

product-inclusion : (d : S) → ⟨ CB.isSubset (GS.product d d) (prodL d) ⟩
product-inclusion d p hp = PT.rec (snd (p ∈ˢ prodL d))
  (λ { (a , b , ha , hb , kp) →
    subst (λ z → ⟨ z ∈ fst (prodL d) ⟩) (sym (ordered-reading p a b kp))
      (prodL-in d a b ha hb) }) (GS.product-out d d p hp)

square : (d : S) → IsOrd (fst d) → ⟨ CB.isCardinal d ⟩
  → ⟨ ωʟ ∈ˢ d ⟩ → ⟨ CB.injectable (GS.product d d) d ⟩
square d od cd wd = CO.injectable-trans separationL replacementL pairingL
  (GS.product d d) (prodL d) d
  (CO.injectable-incl separationL replacementL pairingL
    (GS.product d d) (prodL d) (product-inclusion d))
  (coded-injection (prodL d) d (square-law-L d od (cardinal-internal d cd) wd))

countable-union-bound : (F d : S) → IsOrd (fst d) → ⟨ CB.isCardinal d ⟩
  → ⟨ ωʟ ∈ˢ d ⟩ → ⟨ CB.injectable F d ⟩
  → ((v : S) → ⟨ v ∈ˢ F ⟩ → ⟨ CB.injectable v ωʟ ⟩)
  → ⟨ CB.injectable (UC.FU.bigUnion F) d ⟩
countable-union-bound F d od cd wd hF each = UC.union-bound F d hF each
  (CO.injectable-incl separationL replacementL pairingL ωʟ d
    (λ a ha → cd .fst .fst ωʟ wd a ha)) (square d od cd wd)

proved-range : (d κ : S) → IsOrd (fst d) → ⟨ CB.isCardinal d ⟩
  → ⟨ ωʟ ∈ˢ d ⟩ → ⟨ CB.isCardinal κ ⟩ → ⟨ d ∈ˢ κ ⟩
  → ((β : S) → ⟨ β ∈ˢ κ ⟩ → ⟨ CB.injectable β d ⟩)
  → ⟨ UC.ProvedRange κ ⟩
proved-range d κ od cd wd cκ dκ below = UC.proved-range d κ cκ dκ
  (CO.injectable-incl separationL replacementL pairingL ωʟ d
    (λ a ha → cd .fst .fst ωʟ wd a ha)) below (square d od cd wd)

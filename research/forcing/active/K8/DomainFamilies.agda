{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile

module K8.DomainFamilies
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
  (κ w : ZFStructure.S 𝒮) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _∈̇_; _∧̇_; ∀̇_; ∃̇∈ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At; _^_ )
open import FOL.Manipulation.Renaming using ( renameFo; module Sat )
open import CodedVocabulary 𝒮 using ( subsetΔ; orderAtˢ; sepAt; sepAt-reading )
open import K8.FiniteVocabulary 𝒮 using ( finiteIn )
open import OrdinaryProfile 𝒮 using ( ChoiceSet; module Swap )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )
import CardinalBridge
import GroundDescription
import K8.CohenFibers
import K8.FamilyImages
import K8.FiniteSubsets
import K8.FiniteCountable
import K8.CountableZFC

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )
private
  module CB = CardinalBridge 𝒮
  module GD = GroundDescription 𝒮 ext paths
  module CF = K8.CohenFibers 𝒮 ext paths pair un pow sep κ w
  module C = CF.C
  module PM = C.PM
  module GS = C.GS
  module FI = K8.FamilyImages 𝒮 ext paths pair un pow sep coll find κ
  module FS = K8.FiniteSubsets 𝒮 ext paths pow sep
  module FC = K8.FiniteCountable 𝒮 ext paths pair un pow sep find κ
  module CZ = K8.CountableZFC 𝒮 ext paths pair un pow sep coll find κ
  module Ren = Sat (hPropAlgebra ℓ) 𝒮 id
open CB using ( _↔̇_ )

toEq : {x y : S} → x ≡ y → ⟨ x ≈ˢ y ⟩
toEq {x} {y} = subst ⟨_⟩ (sym (paths x y))

domainFo : Formula S 2
domainFo = ∀̇ ((var zero ∈̇ var (suc zero)) ↔̇
  ((var zero ∈̇ con C.coordinates) ∧̇ ∃̇∈ (con C.two)
    (orderAtˢ (suc (suc (suc zero))) (suc zero) zero)))

domainFo-out : (a p : S) → ⟨ (a ∷ p ∷ []) ⊨ domainFo ⟩ → a ≡ PM.domain p
domainFo-out a p h = GD.ext-path λ x →
  ⇔toPath (h x .fst) (h x .snd) ∙ sym (PM.domain-spec p x)

domainFo-in : (a p : S) → a ≡ PM.domain p → ⟨ (a ∷ p ∷ []) ⊨ domainFo ⟩
domainFo-in a p e x = subst ⟨_⟩ eq , subst ⟨_⟩ (sym eq)
  where
  eq = cong (x ∈ˢ_) e ∙ PM.domain-spec p x

domainAt : ∀ {n} → Fin n → Fin n → Formula S n
domainAt a p = renameFo (λ { zero → a ; (suc zero) → p }) domainFo

domainAt-reading : ∀ {n} (a p : Fin n) (γ : S ^ n)
  → (γ ⊨ domainAt a p) ≡ ((lookup a γ ∷ lookup p γ ∷ []) ⊨ domainFo)
domainAt-reading a p γ = Ren.⊨-rename
  (λ { zero → a ; (suc zero) → p }) domainFo γ
  (lookup a γ ∷ lookup p γ ∷ []) (λ { zero → refl ; (suc zero) → refl })

domain-bound : (p : S) → ⟨ PM.domain p ∈ˢ GS.power C.coordinates ⟩
domain-bound p = subst ⟨_⟩ (sym (GS.power-spec C.coordinates (PM.domain p)))
  (λ x hx → subst ⟨_⟩ (PM.domain-spec p x) hx .fst)

module Family (d : S) (sub : ⟨ subsetΔ d C.carrier ⟩) where
  D : S
  D = FI.imageIn d (GS.power C.coordinates) domainFo

  D-in : (p : S) → ⟨ p ∈ˢ d ⟩ → ⟨ PM.domain p ∈ˢ D ⟩
  D-in p hp = FI.image-in d (GS.power C.coordinates) domainFo p (PM.domain p)
    hp (domain-bound p) (domainFo-in (PM.domain p) p refl)

  D-out : (a : S) → ⟨ a ∈ˢ D ⟩
    → ⟨ ⋁ S (λ p → (p ∈ˢ d) ⊓ (a ≈ˢ PM.domain p)) ⟩
  D-out a ha = PT.map (λ { (p , hp , eq) → p , hp , toEq (domainFo-out a p eq) })
    (FI.image-out d (GS.power C.coordinates) domainFo a ha)

  D-finite : (a : S) → ⟨ a ∈ˢ D ⟩ → ⟨ finiteIn C.coordinates a ⟩
  D-finite a ha = PT.rec (snd (finiteIn C.coordinates a))
    (λ { (p , hp , eq) → subst (λ z → ⟨ finiteIn C.coordinates z ⟩)
      (sym (GS.≈→≡ eq)) (CF.DF.domain-finite p
        (subst ⟨_⟩ (PM.carrier-spec p) (sub p hp) .fst)) }) (D-out a ha)

  D-countable : ChoiceSet → ⟨ CB.injectable d w ⟩ → ⟨ CB.injectable D w ⟩
  D-countable choice = FI.image-countable choice d (GS.power C.coordinates) w domainFo
    (λ p a b hp ha hb ea eb → toEq (domainFo-out a p ea ∙ sym (domainFo-out b p eb)))

  fiberFormula : S → Formula S 1
  fiberFormula a = sepAt (Swap.swapFo domainFo) (a ∷ [])

  fiberFormula-reading : (a p : S)
    → ((p ∷ []) ⊨ fiberFormula a) ≡ ((a ∷ p ∷ []) ⊨ domainFo)
  fiberFormula-reading a p = sepAt-reading (Swap.swapFo domainFo) (a ∷ []) p
    ∙ Swap.⊨-swap domainFo p a

  opaque
    fiber : S → S
    fiber a = GS.separator d (fiberFormula a)

    fiber-spec : (a p : S) → (p ∈ˢ fiber a)
      ≡ ((p ∈ˢ d) ⊓ ((a ∷ p ∷ []) ⊨ domainFo))
    fiber-spec a p = GS.separator-spec d (fiberFormula a) p
      ∙ cong ((p ∈ˢ d) ⊓_) (fiberFormula-reading a p)

  fiber-sub : (a : S) → ⟨ subsetΔ (fiber a) d ⟩
  fiber-sub a p hp = subst ⟨_⟩ (fiber-spec a p) hp .fst

  fiber-self : (p : S) → ⟨ p ∈ˢ d ⟩ → ⟨ p ∈ˢ fiber (PM.domain p) ⟩
  fiber-self p hp = subst ⟨_⟩ (sym (fiber-spec (PM.domain p) p))
    (hp , domainFo-in (PM.domain p) p refl)

  fiber-finite : LEM ℓ → (a : S) → ⟨ a ∈ˢ D ⟩ → ⟨ finiteIn C.carrier (fiber a) ⟩
  fiber-finite lem a ha = FS.finite-subset lem C.carrier (CF.F.fiber a) (fiber a)
    (CF.F.finite-fiber lem a (D-finite a ha) CF.two-finite)
    (λ p hp → CF.F.fiber-in a p (sub p (fiber-sub a p hp))
      (λ x hx → subst (λ z → ⟨ x ∈ˢ z ⟩)
        (sym (domainFo-out a p (subst ⟨_⟩ (fiber-spec a p) hp .snd))) hx))

  fiberFo : Formula S 2
  fiberFo = ∀̇ ((var zero ∈̇ var (suc zero)) ↔̇
    ((var zero ∈̇ con d) ∧̇ domainAt (suc (suc zero)) zero))

  fiberFo-out : (f a : S) → ⟨ (f ∷ a ∷ []) ⊨ fiberFo ⟩ → f ≡ fiber a
  fiberFo-out f a h = GD.ext-path λ p → ⇔toPath (h p .fst) (h p .snd)
    ∙ cong ((p ∈ˢ d) ⊓_) (domainAt-reading (suc (suc zero)) zero (p ∷ f ∷ a ∷ []))
    ∙ sym (fiber-spec a p)

  fiberFo-in : (f a : S) → f ≡ fiber a → ⟨ (f ∷ a ∷ []) ⊨ fiberFo ⟩
  fiberFo-in f a e p = subst ⟨_⟩ eq , subst ⟨_⟩ (sym eq)
    where
    eq = cong (p ∈ˢ_) e ∙ fiber-spec a p
      ∙ cong ((p ∈ˢ d) ⊓_) (sym (domainAt-reading (suc (suc zero)) zero (p ∷ f ∷ a ∷ [])))

  F : S
  F = FI.imageIn D (GS.power d) fiberFo

  F-in : (a : S) → ⟨ a ∈ˢ D ⟩ → ⟨ fiber a ∈ˢ F ⟩
  F-in a ha = FI.image-in D (GS.power d) fiberFo a (fiber a) ha
    (subst ⟨_⟩ (sym (GS.power-spec d (fiber a))) (fiber-sub a))
    (fiberFo-in (fiber a) a refl)

  F-out : (f : S) → ⟨ f ∈ˢ F ⟩
    → ⟨ ⋁ S (λ a → (a ∈ˢ D) ⊓ (f ≈ˢ fiber a)) ⟩
  F-out f hf = PT.map (λ { (a , ha , eq) → a , ha , toEq (fiberFo-out f a eq) })
    (FI.image-out D (GS.power d) fiberFo f hf)

  conditions-countable : LEM ℓ → ChoiceSet → ⟨ CB.isOmega w ⟩
    → ⟨ CB.injectable D w ⟩ → ⟨ CB.injectable d w ⟩
  conditions-countable lem choice hw countD = Z.countable-union F d
    (λ f hf → subst ⟨_⟩ (GS.power-spec d f)
      (FI.image-sub D (GS.power d) fiberFo f hf))
    (λ p hp → ∣ fiber (PM.domain p) , F-in (PM.domain p) (D-in p hp) , fiber-self p hp ∣₁)
    (FI.image-countable choice D (GS.power d) w fiberFo
      (λ a f g ha hf hg ef eg → toEq (fiberFo-out f a ef ∙ sym (fiberFo-out g a eg))) countD)
    (λ f hf → PT.rec (snd (CB.injectable f w))
      (λ { (a , ha , eq) → subst (λ z → ⟨ CB.injectable z w ⟩)
        (sym (GS.≈→≡ eq)) (FC.finite-countable lem w hw C.carrier (fiber a)
          (fiber-finite lem a ha)) }) (F-out f hf))
    where module Z = CZ.AtOmega lem choice w hw

{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile

module InternalCohenReals
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (families : NameKernel.Families 𝒮)
  (accessible : NameKernel.Accessibility 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (κ w : ZFStructure.S 𝒮)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; Term; var; con; _∈̇_; _∧̇_; _⇒̇_; ∀̇_; ∃̇_; ∃̇∈ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
open import CodedVocabulary 𝒮 using
  ( refinesΔ; isKPairΔ; orderAtˢ; prAtˢ; sepAt; sepAt-reading; instFo; ⊨-inst )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )
import K8.Cohen
import K8.GroundSets
import InternalWeightedCheck
import WeightedCheckRecursion
import NameImage

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )
open NameKernel.Families families using ( sets; hasCollect )
open NameKernel.Sets sets using ( core; hasUnion; hasSeparation )
open NameKernel.Core core using ( extensional; hasPair; ≈ˢ-paths )

module C = K8.Cohen 𝒮 extensional ≈ˢ-paths hasPair hasUnion pow hasSeparation κ w
  using ( carrier; coordinate; bit₁ )
module GS = K8.GroundSets.Ground 𝒮 extensional ≈ˢ-paths hasPair hasUnion pow hasSeparation κ
  using ( separator; separator-spec; ordered; ordered-witness; ordered-unique
        ; product; product-in; product-out; singleton; singleton-witness; ≈→≡ )
module K = NameKernel.Kernel 𝒮 core accessible C.carrier
  using ( entry; entry-inj; entry-isKPair; IsName; Name; Child; Shape; name-intro )
module Check = InternalWeightedCheck 𝒮 families accessible pow C.carrier
  using ( chk; chk-name )
module Rec = WeightedCheckRecursion.Construct 𝒮 extensional ≈ˢ-paths accessible C.carrier
  hasPair hasUnion pow hasSeparation hasCollect C.carrier
  using ( check-image; table; table-mem; table-only; module GS )
module RG = Rec.GS using ( ordered; ordered-witness )
module NI = NameImage 𝒮 extensional ≈ˢ-paths using ( InternalImage; DefinableGraph; graph→internal )

private
  i0 : ∀ {n} → Fin (suc n)
  i0 = zero
  i1 : ∀ {n} → Fin (suc (suc n))
  i1 = suc i0
  i2 : ∀ {n} → Fin (suc (suc (suc n)))
  i2 = suc i1
  i3 : ∀ {n} → Fin (suc (suc (suc (suc n))))
  i3 = suc i2
  i4 : ∀ {n} → Fin (suc (suc (suc (suc (suc n)))))
  i4 = suc i3
  i5 : ∀ {n} → Fin (suc (suc (suc (suc (suc (suc n))))))
  i5 = suc i4
  i6 : ∀ {n} → Fin (suc (suc (suc (suc (suc (suc (suc n)))))))
  i6 = suc i5
  i7 : ∀ {n} → Fin (suc (suc (suc (suc (suc (suc (suc (suc n))))))))
  i7 = suc i6
  i8 : ∀ {n} → Fin (suc (suc (suc (suc (suc (suc (suc (suc (suc n)))))))))
  i8 = suc i7

entry-agrees : (x p : S) → GS.ordered x p ≡ K.entry x p
entry-agrees x p = sym (GS.ordered-unique (K.entry x p) x p (K.entry-isKPair x p))

checkTable : S
checkTable = Rec.table w

check-ref : (n : S) → ⟨ n ∈ˢ w ⟩ → ⟨ refinesΔ checkTable n (Check.chk n) ⟩
check-ref n hn = ∣ RG.ordered n (Check.chk n) , Rec.table-mem w n hn ,
  RG.ordered-witness n (Check.chk n) ∣₁

check-only : (n t : S) → ⟨ n ∈ˢ w ⟩ → ⟨ refinesΔ checkTable n t ⟩ → t ≡ Check.chk n
check-only n t hn = PT.rec (isSetS t (Check.chk n))
  λ { (e , he , kp) → Rec.table-only w e n t hn he kp }

supportBound : S
supportBound = NI.InternalImage.img Rec.check-image w

support-spec : (x : S) → (x ∈ˢ supportBound) ≡
  ⋁ S (λ n → (n ∈ˢ w) ⊓ (x ≈ˢ Check.chk n))
support-spec = NI.InternalImage.img-spec Rec.check-image w

Raw : S → S → Ω
Raw α e = ⋁ S (λ n → (n ∈ˢ w) ⊓ ⋁ S (λ p → (p ∈ˢ C.carrier) ⊓
  ⋁ S (λ t → refinesΔ checkTable n t ⊓ (isKPairΔ e t p ⊓
    ⋁ S (λ c → isKPairΔ c α n ⊓ refinesΔ p c C.bit₁)))))

rawFo : Formula S 6
rawFo = ∃̇∈ (var i2) (∃̇∈ (var i4) (∃̇
  (orderAtˢ (suc i7) i2 i0 ∧̇ (prAtˢ i3 i0 i1 ∧̇
    ∃̇ (prAtˢ i0 i5 i3 ∧̇ orderAtˢ i2 i0 i8)))))

rawAt : S → Formula S 1
rawAt α = sepAt rawFo (α ∷ w ∷ C.carrier ∷ C.bit₁ ∷ checkTable ∷ [])

raw-reading : (α e : S) → ((e ∷ []) ⊨ rawAt α) ≡ Raw α e
raw-reading α e = sepAt-reading rawFo (α ∷ w ∷ C.carrier ∷ C.bit₁ ∷ checkTable ∷ []) e

Target : S → S → Ω
Target α e = ⋁ S (λ n → (n ∈ˢ w) ⊓ ⋁ S (λ p → (p ∈ˢ C.carrier) ⊓
  (refinesΔ p (C.coordinate α n) C.bit₁ ⊓ (e ≈ˢ K.entry (Check.chk n) p))))

raw→target : (α e : S) → ⟨ Raw α e ⟩ → ⟨ Target α e ⟩
raw→target α e = PT.rec PT.squash₁ λ { (n , hn , ps) →
  PT.rec PT.squash₁ (λ { (p , hp , ts) → PT.rec PT.squash₁
    (λ { (t , ht , kp , cs) → PT.map (λ { (c , hc , bit) → n , hn , ∣ p , hp ,
      subst (λ j → ⟨ refinesΔ p j C.bit₁ ⟩) (GS.ordered-unique c α n hc) bit ,
      subst ⟨_⟩ (sym (≈ˢ-paths e (K.entry (Check.chk n) p)))
        (GS.ordered-unique e t p kp ∙ cong (λ j → GS.ordered j p) (check-only n t hn ht) ∙
          entry-agrees (Check.chk n) p) ∣₁ }) cs }) ts }) ps }

target→raw : (α e : S) → ⟨ Target α e ⟩ → ⟨ Raw α e ⟩
target→raw α e = PT.map λ { (n , hn , ps) → n , hn ,
  PT.map (λ { (p , hp , bit , ep) → p , hp , ∣ Check.chk n , check-ref n hn ,
    subst (λ j → ⟨ isKPairΔ j (Check.chk n) p ⟩) (sym (GS.≈→≡ ep))
      (K.entry-isKPair (Check.chk n) p) ,
    ∣ C.coordinate α n , GS.ordered-witness α n , bit ∣₁ ∣₁ }) ps }

bound : S
bound = GS.product supportBound C.carrier

target-bound : (α e : S) → ⟨ Target α e ⟩ → ⟨ e ∈ˢ bound ⟩
target-bound α e = PT.rec (snd (e ∈ˢ bound)) λ { (n , hn , ps) →
  PT.rec (snd (e ∈ˢ bound)) (λ { (p , hp , bit , ep) →
    subst (λ j → ⟨ j ∈ˢ bound ⟩) (entry-agrees (Check.chk n) p ∙ sym (GS.≈→≡ ep))
      (GS.product-in supportBound C.carrier (Check.chk n) p
        (subst ⟨_⟩ (sym (support-spec (Check.chk n)))
          ∣ n , hn , subst ⟨_⟩ (sym (≈ˢ-paths (Check.chk n) (Check.chk n))) refl ∣₁) hp) }) ps }

opaque
  realCode : S → S
  realCode α = GS.separator bound (rawAt α)

  real-spec : (α e : S) → (e ∈ˢ realCode α) ≡ Target α e
  real-spec α e = ⇔toPath
    (λ h → raw→target α e (subst ⟨_⟩ (raw-reading α e)
      (subst ⟨_⟩ (GS.separator-spec bound (rawAt α) e) h .snd)))
    (λ h → subst ⟨_⟩ (sym (GS.separator-spec bound (rawAt α) e))
      (target-bound α e h , subst ⟨_⟩ (sym (raw-reading α e)) (target→raw α e h)))

real-name : (α : S) → ⟨ K.IsName (realCode α) ⟩
real-name α = K.name-intro (realCode α) shape hereditary
  where
  shape : ⟨ K.Shape (realCode α) ⟩
  shape e he = PT.rec PT.squash₁ (λ { (n , hn , ps) →
    PT.map (λ { (p , hp , bit , ep) → Check.chk n , p , GS.≈→≡ ep , hp }) ps })
    (subst ⟨_⟩ (real-spec α e) he)

  hereditary : (x : S) → K.Child x (realCode α) → ⟨ K.IsName x ⟩
  hereditary x = PT.rec (snd (K.IsName x)) λ { (b , hb) →
    PT.rec (snd (K.IsName x)) (λ { (n , hn , ps) → PT.rec (snd (K.IsName x))
      (λ { (p , hp , bit , ep) → subst (λ j → ⟨ K.IsName j ⟩)
        (sym (K.entry-inj (GS.≈→≡ ep) .fst)) (Check.chk-name n) }) ps })
      (subst ⟨_⟩ (real-spec α (K.entry x b)) hb) }

real : S → K.Name
real α = realCode α , real-name α

real-entry : (α n p : S) → ⟨ n ∈ˢ w ⟩ → ⟨ p ∈ˢ C.carrier ⟩
  → ⟨ refinesΔ p (C.coordinate α n) C.bit₁ ⟩ → ⟨ K.entry (Check.chk n) p ∈ˢ realCode α ⟩
real-entry α n p hn hp bit = subst ⟨_⟩ (sym (real-spec α (K.entry (Check.chk n) p)))
  ∣ n , hn , ∣ p , hp , bit , subst ⟨_⟩
    (sym (≈ˢ-paths (K.entry (Check.chk n) p) (K.entry (Check.chk n) p))) refl ∣₁ ∣₁

real-support : (α x : S) → K.Child x (realCode α) → ⟨ x ∈ˢ supportBound ⟩
real-support α x = PT.rec (snd (x ∈ˢ supportBound)) λ { (b , hb) →
  PT.rec (snd (x ∈ˢ supportBound)) (λ { (n , hn , ps) → PT.rec (snd (x ∈ˢ supportBound))
    (λ { (p , hp , bit , ep) → subst ⟨_⟩ (sym (support-spec x))
      ∣ n , hn , subst ⟨_⟩ (sym (≈ˢ-paths x (Check.chk n)))
        (K.entry-inj (GS.≈→≡ ep) .fst) ∣₁ }) ps })
    (subst ⟨_⟩ (real-spec α (K.entry x b)) hb) }

open import GroundDescription 𝒮 extensional ≈ˢ-paths using ( ext-path )

private
  graphSub : Fin 6 → Term S 3
  graphSub zero = var i0
  graphSub (suc zero) = var i2
  graphSub (suc (suc zero)) = con w
  graphSub (suc (suc (suc zero))) = con C.carrier
  graphSub (suc (suc (suc (suc zero)))) = con C.bit₁
  graphSub (suc (suc (suc (suc (suc zero))))) = con checkTable

  body : Formula S 3
  body = instFo graphSub rawFo

  body-reading : (e v α : S) → ((e ∷ v ∷ α ∷ []) ⊨ body) ≡ Raw α e
  body-reading e v α = ⊨-inst graphSub rawFo (e ∷ v ∷ α ∷ [])
    (e ∷ α ∷ w ∷ C.carrier ∷ C.bit₁ ∷ checkTable ∷ [])
    λ { zero → refl; (suc zero) → refl; (suc (suc zero)) → refl
      ; (suc (suc (suc zero))) → refl; (suc (suc (suc (suc zero)))) → refl
      ; (suc (suc (suc (suc (suc zero))))) → refl }

realGraph : Formula S 2
realGraph = ∀̇ (((var i0 ∈̇ var i1) ⇒̇ body) ∧̇ (body ⇒̇ (var i0 ∈̇ var i1)))

real-graph : NI.DefinableGraph realCode
real-graph = record
  { graph = realGraph
  ; defines = λ α e →
      (λ h → subst ⟨_⟩ (sym (body-reading e (realCode α) α))
        (target→raw α e (subst ⟨_⟩ (real-spec α e) h))) ,
      (λ h → subst ⟨_⟩ (sym (real-spec α e))
        (raw→target α e (subst ⟨_⟩ (body-reading e (realCode α) α) h)))
  ; only = λ α v h → ext-path λ e → ⇔toPath
      (λ he → subst ⟨_⟩ (sym (real-spec α e))
        (raw→target α e (subst ⟨_⟩ (body-reading e v α) (h e .fst he))))
      (λ he → h e .snd (subst ⟨_⟩ (sym (body-reading e v α))
        (target→raw α e (subst ⟨_⟩ (real-spec α e) he))))
  }

real-image : NI.InternalImage realCode
real-image = NI.graph→internal hasCollect hasSeparation realCode real-graph

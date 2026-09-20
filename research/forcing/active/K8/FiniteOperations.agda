{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile

module K8.FiniteOperations
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
open import FOL.Syntax using ( Formula; var; _⇒̇_; ∀̇_ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
open import CodedVocabulary 𝒮 using ( subsetΔ; sepAt; sepAt-reading )
open import K8.FiniteVocabulary 𝒮
  using ( finiteIn; finiteAt; emptyPred; adjoinPred; unionPred; unionAt )
open import K8.FiniteSets 𝒮 ext paths pow sep
  using ( finite-empty; finite-adjoin; finite-induction )
import K8.GroundSets
module GS = K8.GroundSets.Ground 𝒮 ext paths pair un pow sep seed
open GS using ( empty; empty-out; singleton; singleton-witness; join; join-spec; ≈→≡ )
open import GroundDescription 𝒮 ext paths using ( ext-path )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.Data.Sum using ( _⊎_ ) renaming ( inl to inl⊎; inr to inr⊎ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )
import Cubical.Data.Empty as Empty

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )

join-inˡ : (a b z : S) → ⟨ z ∈ˢ a ⟩ → ⟨ z ∈ˢ join a b ⟩
join-inˡ a b z h = subst ⟨_⟩ (sym (join-spec a b z)) ∣ inl⊎ h ∣₁

join-inʳ : (a b z : S) → ⟨ z ∈ˢ b ⟩ → ⟨ z ∈ˢ join a b ⟩
join-inʳ a b z h = subst ⟨_⟩ (sym (join-spec a b z)) ∣ inr⊎ h ∣₁

insert : S → S → S
insert a x = join a (singleton x)

insert-witness : (a x : S) → ⟨ adjoinPred (insert a x) a x ⟩
insert-witness a x = join-inʳ a (singleton x) x (fst (singleton-witness x))
  , join-inˡ a (singleton x)
  , (λ z hz → PT.map
      (λ { (inl⊎ ha) → inl⊎ ha
         ; (inr⊎ hx) → inr⊎ (snd (singleton-witness x) z hx) })
      (subst ⟨_⟩ (join-spec a (singleton x) z) hz))

finite-insert : (X a x : S) → ⟨ finiteIn X a ⟩ → ⟨ x ∈ˢ X ⟩
  → ⟨ finiteIn X (insert a x) ⟩
finite-insert X a x ha hx = finite-adjoin X (insert a x) a x ha hx (insert-witness a x)

join-witness : (a b : S) → ⟨ unionPred (join a b) a b ⟩
join-witness a b z = subst ⟨_⟩ (join-spec a b z)
  , subst ⟨_⟩ (sym (join-spec a b z))

union-unique : (u a b : S) → ⟨ unionPred u a b ⟩ → u ≡ join a b
union-unique u a b h = ext-path (λ z →
  ⇔toPath (fst (h z)) (snd (h z)) ∙ sym (join-spec a b z))

join-empty : (e b : S) → ⟨ emptyPred e ⟩ → join e b ≡ b
join-empty e b he = ext-path (λ z → join-spec e b z ∙ ⇔toPath
  (PT.rec (snd (z ∈ˢ b)) (λ { (inl⊎ h) → Empty.rec* (he z h); (inr⊎ h) → h }))
  (λ h → ∣ inr⊎ h ∣₁))

join-adjoin : (u a b x : S) → ⟨ adjoinPred u a x ⟩
  → ⟨ adjoinPred (join u b) (join a b) x ⟩
join-adjoin u a b x hu = join-inˡ u b x (fst hu) , sub , all
  where
  sub : ⟨ subsetΔ (join a b) (join u b) ⟩
  sub z hz = PT.rec (snd (z ∈ˢ join u b))
    (λ { (inl⊎ ha) → join-inˡ u b z (fst (snd hu) z ha)
       ; (inr⊎ hb) → join-inʳ u b z hb })
    (subst ⟨_⟩ (join-spec a b z) hz)

  all : (z : S) → ⟨ z ∈ˢ join u b ⟩
    → ⟨ (z ∈ˢ join a b) ⊔ (z ≈ˢ x) ⟩
  all z hz = PT.rec (snd ((z ∈ˢ join a b) ⊔ (z ≈ˢ x)))
    (λ { (inl⊎ hz') → PT.map
          (λ { (inl⊎ ha) → inl⊎ (join-inˡ a b z ha); (inr⊎ hx) → inr⊎ hx })
          (snd (snd hu) z hz')
       ; (inr⊎ hb) → ∣ inl⊎ (join-inʳ a b z hb) ∣₁ })
    (subst ⟨_⟩ (join-spec u b z) hz)

joinFiniteAt : Formula S 3
joinFiniteAt = ∀̇ (unionAt zero (suc zero) (suc (suc zero))
  ⇒̇ finiteAt (suc (suc (suc zero))) zero)

joinFiniteFormula : S → S → Formula S 1
joinFiniteFormula b X = sepAt joinFiniteAt (b ∷ X ∷ [])

joinFinite-reading : (a b X : S)
  → ((a ∷ []) ⊨ joinFiniteFormula b X)
    ≡ (⋀ S (λ u → unionPred u a b ⇒ finiteIn X u))
joinFinite-reading a b X = sepAt-reading joinFiniteAt (b ∷ X ∷ []) a

finite-join : (X a b : S) → ⟨ finiteIn X a ⟩ → ⟨ finiteIn X b ⟩
  → ⟨ finiteIn X (join a b) ⟩
finite-join X a b ha hb =
  subst ⟨_⟩ (joinFinite-reading a b X)
    (finite-induction X (joinFiniteFormula b X) base step a ha)
    (join a b) (join-witness a b)
  where
  base : (e : S) → ⟨ emptyPred e ⟩ → ⟨ (e ∷ []) ⊨ joinFiniteFormula b X ⟩
  base e he = subst ⟨_⟩ (sym (joinFinite-reading e b X))
    (λ u hu → subst (λ z → ⟨ finiteIn X z ⟩)
      (sym (union-unique u e b hu ∙ join-empty e b he)) hb)

  step : (a' u x : S) → ⟨ finiteIn X a' ⟩
    → ⟨ (a' ∷ []) ⊨ joinFiniteFormula b X ⟩
    → ⟨ x ∈ˢ X ⟩ → ⟨ adjoinPred u a' x ⟩
    → ⟨ (u ∷ []) ⊨ joinFiniteFormula b X ⟩
  step a' u x ha' ih hx hu = subst ⟨_⟩ (sym (joinFinite-reading u b X))
    (λ v hv → subst (λ z → ⟨ finiteIn X z ⟩) (sym (union-unique v u b hv))
      (finite-adjoin X (join u b) (join a' b) x
        (subst ⟨_⟩ (joinFinite-reading a' b X) ih (join a' b) (join-witness a' b))
        hx (join-adjoin u a' b x hu)))

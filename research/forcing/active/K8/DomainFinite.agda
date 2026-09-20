{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile

module K8.DomainFinite
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
open import FOL.Syntax using ( Formula; var; _∈̇_; _∧̇_; _⇒̇_; ∀̇_ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
open import CodedVocabulary 𝒮 using ( subsetΔ; isKPairΔ; refinesΔ; sepAt; sepAt-reading )
open import CardinalBridge 𝒮 using ( _↔̇_ )
open import OrdinaryProfile 𝒮 using ( iff )
open import K8.FiniteVocabulary 𝒮 using ( finiteIn; finiteAt; emptyPred; adjoinPred )
open import K8.MapVocabulary 𝒮 using ( domainPred; domainAt )
open import K8.FiniteSets 𝒮 ext paths pow sep
  using ( finite-empty; finite-adjoin; finite-induction )
import K8.GroundSets
import K8.PartialMaps
module GS = K8.GroundSets.Ground 𝒮 ext paths pair un pow sep seed
module PM = K8.PartialMaps.Maps 𝒮 ext paths pair un pow sep seed X Y
open import GroundDescription 𝒮 ext paths using ( ext-path )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.Data.Sum using ( _⊎_ ) renaming ( inl to inl⊎; inr to inr⊎ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )
import Cubical.Data.Empty as Empty

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )

domainSpec : S → S → Ω
domainSpec d a = ⋀ S (λ z → iff (z ∈ˢ d) ((z ∈ˢ X) ⊓ domainPred Y a z))

domainSpecAt : Formula S 4
domainSpecAt = ∀̇ ((var zero ∈̇ var (suc zero)) ↔̇
  ((var zero ∈̇ var (suc (suc (suc zero))))
    ∧̇ domainAt (suc (suc (suc (suc zero)))) (suc (suc zero)) zero))

domainFiniteAt : Formula S 3
domainFiniteAt = ∀̇ (domainSpecAt ⇒̇ finiteAt (suc (suc zero)) zero)

domainFiniteFormula : Formula S 1
domainFiniteFormula = sepAt domainFiniteAt (X ∷ Y ∷ [])

domainFinite-reading : (a : S)
  → ((a ∷ []) ⊨ domainFiniteFormula)
    ≡ (⋀ S (λ d → domainSpec d a ⇒ finiteIn X d))
domainFinite-reading a = sepAt-reading domainFiniteAt (X ∷ Y ∷ []) a

domain-witness : (a : S) → ⟨ domainSpec (PM.domain a) a ⟩
domain-witness a z = subst ⟨_⟩ (PM.domain-spec a z)
  , subst ⟨_⟩ (sym (PM.domain-spec a z))

domain-unique : (d a : S) → ⟨ domainSpec d a ⟩ → d ≡ PM.domain a
domain-unique d a h = ext-path (λ z →
  ⇔toPath (fst (h z)) (snd (h z)) ∙ sym (PM.domain-spec a z))

domain-adjoin : (b a p x y : S) → ⟨ adjoinPred b a p ⟩
  → ⟨ x ∈ˢ X ⟩ → ⟨ y ∈ˢ Y ⟩ → ⟨ isKPairΔ p x y ⟩
  → ⟨ adjoinPred (PM.domain b) (PM.domain a) x ⟩
domain-adjoin b a p x y hb hx hy hp =
  PM.domain-in b x y hx hy ∣ p , fst hb , hp ∣₁ , sub , all
  where
  sub : ⟨ subsetΔ (PM.domain a) (PM.domain b) ⟩
  sub z hz = subst ⟨_⟩ (sym (PM.domain-spec b z))
    (fst old , PT.map (λ { (v , hv , hpair) → v , hv ,
      PT.map (λ { (q , hq , qp) → q , fst (snd hb) q hq , qp }) hpair }) (snd old))
    where
    old : ⟨ (z ∈ˢ X) ⊓ domainPred Y a z ⟩
    old = subst ⟨_⟩ (PM.domain-spec a z) hz

  all : (z : S) → ⟨ z ∈ˢ PM.domain b ⟩ → ⟨ (z ∈ˢ PM.domain a) ⊔ (z ≈ˢ x) ⟩
  all z hz = PT.rec (snd ((z ∈ˢ PM.domain a) ⊔ (z ≈ˢ x)))
    atValue (snd data')
    where
    data' : ⟨ (z ∈ˢ X) ⊓ domainPred Y b z ⟩
    data' = subst ⟨_⟩ (PM.domain-spec b z) hz

    atValue : Σ[ v ∈ S ] (⟨ v ∈ˢ Y ⟩ × ⟨ refinesΔ b z v ⟩)
      → ⟨ (z ∈ˢ PM.domain a) ⊔ (z ≈ˢ x) ⟩
    atValue (v , hv , hpair) = PT.rec (snd ((z ∈ˢ PM.domain a) ⊔ (z ≈ˢ x)))
      atPair hpair
      where
      atPair : Σ[ q ∈ S ] (⟨ q ∈ˢ b ⟩ × ⟨ isKPairΔ q z v ⟩)
        → ⟨ (z ∈ˢ PM.domain a) ⊔ (z ≈ˢ x) ⟩
      atPair (q , hq , qp) = PT.map branch (snd (snd hb) q hq)
        where
        branch : ⟨ q ∈ˢ a ⟩ ⊎ ⟨ q ≈ˢ p ⟩
          → ⟨ z ∈ˢ PM.domain a ⟩ ⊎ ⟨ z ≈ˢ x ⟩
        branch (inl⊎ qa) = inl⊎ (PM.domain-in a z v (fst data') hv ∣ q , qa , qp ∣₁)
        branch (inr⊎ eq) = inr⊎ (subst ⟨_⟩ (sym (paths z x))
          (fst (GS.ordered-components p z v x y
            (subst (λ t → ⟨ isKPairΔ t z v ⟩) (GS.≈→≡ eq) qp) hp)))

domain-finite : (a : S) → ⟨ finiteIn PM.W a ⟩ → ⟨ finiteIn X (PM.domain a) ⟩
domain-finite a ha = subst ⟨_⟩ (domainFinite-reading a)
  (finite-induction PM.W domainFiniteFormula base step a ha)
  (PM.domain a) (domain-witness a)
  where
  base : (e : S) → ⟨ emptyPred e ⟩ → ⟨ (e ∷ []) ⊨ domainFiniteFormula ⟩
  base e he = subst ⟨_⟩ (sym (domainFinite-reading e))
    (λ d hd → finite-empty X d (λ z hz → PT.rec (snd ⊥)
      (λ { (v , hv , hp) → PT.rec (snd ⊥) (λ { (p , hpe , _) → he p hpe }) hp })
      (snd (fst (hd z) hz))))

  step : (a' b p : S) → ⟨ finiteIn PM.W a' ⟩
    → ⟨ (a' ∷ []) ⊨ domainFiniteFormula ⟩
    → ⟨ p ∈ˢ PM.W ⟩ → ⟨ adjoinPred b a' p ⟩
    → ⟨ (b ∷ []) ⊨ domainFiniteFormula ⟩
  step a' b p ha' ih hp hb = subst ⟨_⟩ (sym (domainFinite-reading b))
    (λ d hd → subst (λ t → ⟨ finiteIn X t ⟩) (sym (domain-unique d b hd))
      (PT.rec (snd (finiteIn X (PM.domain b)))
        (λ { (x , y , hx , hy , kp) →
          finite-adjoin X (PM.domain b) (PM.domain a') x
            (subst ⟨_⟩ (domainFinite-reading a') ih (PM.domain a') (domain-witness a'))
            hx (domain-adjoin b a' p x y hb hx hy kp) })
        (GS.product-out X Y p hp)))

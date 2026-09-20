{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile

module K8.RangeFinite
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
open import FOL.Syntax using ( Formula; var; _∈̇_; _∧̇_; _⇒̇_; ∀̇_; ∃̇∈ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
open import CodedVocabulary 𝒮
  using ( subsetΔ; isKPairΔ; refinesΔ; orderAtˢ; sepAt; sepAt-reading )
open import CardinalBridge 𝒮 using ( _↔̇_ )
open import OrdinaryProfile 𝒮 using ( iff )
open import K8.FiniteVocabulary 𝒮 using ( finiteIn; finiteAt; emptyPred; adjoinPred )
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

rangePred : S → S → Ω
rangePred a y = ⋁ S (λ x → (x ∈ˢ X) ⊓ refinesΔ a x y)

rangeAt : Formula S 3
rangeAt = ∃̇∈ (var (suc (suc zero)))
  (orderAtˢ (suc (suc zero)) zero (suc zero))

rangeFormula : S → Formula S 1
rangeFormula a = sepAt rangeAt (a ∷ X ∷ [])

rangeFormula-reading : (a y : S)
  → ((y ∷ []) ⊨ rangeFormula a) ≡ rangePred a y
rangeFormula-reading a y = sepAt-reading rangeAt (a ∷ X ∷ []) y

opaque
  range : S → S
  range a = GS.separator Y (rangeFormula a)

  range-spec : (a y : S)
    → (y ∈ˢ range a) ≡ ((y ∈ˢ Y) ⊓ rangePred a y)
  range-spec a y = GS.separator-spec Y (rangeFormula a) y
    ∙ cong ((y ∈ˢ Y) ⊓_) (rangeFormula-reading a y)

range-in : (a x y : S) → ⟨ x ∈ˢ X ⟩ → ⟨ y ∈ˢ Y ⟩
  → ⟨ refinesΔ a x y ⟩ → ⟨ y ∈ˢ range a ⟩
range-in a x y hx hy h = subst ⟨_⟩ (sym (range-spec a y))
  (hy , ∣ x , hx , h ∣₁)

rangeSpec : S → S → Ω
rangeSpec r a = ⋀ S (λ z → iff (z ∈ˢ r) ((z ∈ˢ Y) ⊓ rangePred a z))

rangeSpecAt : Formula S 4
rangeSpecAt = ∀̇ ((var zero ∈̇ var (suc zero)) ↔̇
  ((var zero ∈̇ var (suc (suc (suc (suc zero)))))
    ∧̇ (∃̇∈ (var (suc (suc (suc zero))))
      (orderAtˢ (suc (suc (suc zero))) zero (suc zero)))))

rangeFiniteAt : Formula S 3
rangeFiniteAt = ∀̇ (rangeSpecAt ⇒̇ finiteAt (suc (suc (suc zero))) zero)

rangeFiniteFormula : Formula S 1
rangeFiniteFormula = sepAt rangeFiniteAt (X ∷ Y ∷ [])

rangeFinite-reading : (a : S)
  → ((a ∷ []) ⊨ rangeFiniteFormula)
    ≡ (⋀ S (λ r → rangeSpec r a ⇒ finiteIn Y r))
rangeFinite-reading a = sepAt-reading rangeFiniteAt (X ∷ Y ∷ []) a

range-witness : (a : S) → ⟨ rangeSpec (range a) a ⟩
range-witness a z = subst ⟨_⟩ (range-spec a z)
  , subst ⟨_⟩ (sym (range-spec a z))

range-unique : (r a : S) → ⟨ rangeSpec r a ⟩ → r ≡ range a
range-unique r a h = ext-path (λ z →
  ⇔toPath (fst (h z)) (snd (h z)) ∙ sym (range-spec a z))

range-adjoin : (b a p x y : S) → ⟨ adjoinPred b a p ⟩
  → ⟨ x ∈ˢ X ⟩ → ⟨ y ∈ˢ Y ⟩ → ⟨ isKPairΔ p x y ⟩
  → ⟨ adjoinPred (range b) (range a) y ⟩
range-adjoin b a p x y hb hx hy hp =
  range-in b x y hx hy ∣ p , fst hb , hp ∣₁ , sub , all
  where
  sub : ⟨ subsetΔ (range a) (range b) ⟩
  sub z hz = subst ⟨_⟩ (sym (range-spec b z))
    (fst old , PT.map (λ { (v , hv , hpair) → v , hv ,
      PT.map (λ { (q , hq , qp) → q , fst (snd hb) q hq , qp }) hpair }) (snd old))
    where
    old : ⟨ (z ∈ˢ Y) ⊓ rangePred a z ⟩
    old = subst ⟨_⟩ (range-spec a z) hz

  all : (z : S) → ⟨ z ∈ˢ range b ⟩ → ⟨ (z ∈ˢ range a) ⊔ (z ≈ˢ y) ⟩
  all z hz = PT.rec (snd ((z ∈ˢ range a) ⊔ (z ≈ˢ y))) atInput (snd data')
    where
    data' : ⟨ (z ∈ˢ Y) ⊓ rangePred b z ⟩
    data' = subst ⟨_⟩ (range-spec b z) hz

    atInput : Σ[ v ∈ S ] (⟨ v ∈ˢ X ⟩ × ⟨ refinesΔ b v z ⟩)
      → ⟨ (z ∈ˢ range a) ⊔ (z ≈ˢ y) ⟩
    atInput (v , hv , hpair) = PT.rec (snd ((z ∈ˢ range a) ⊔ (z ≈ˢ y)))
      atPair hpair
      where
      atPair : Σ[ q ∈ S ] (⟨ q ∈ˢ b ⟩ × ⟨ isKPairΔ q v z ⟩)
        → ⟨ (z ∈ˢ range a) ⊔ (z ≈ˢ y) ⟩
      atPair (q , hq , qp) = PT.map branch (snd (snd hb) q hq)
        where
        branch : ⟨ q ∈ˢ a ⟩ ⊎ ⟨ q ≈ˢ p ⟩
          → ⟨ z ∈ˢ range a ⟩ ⊎ ⟨ z ≈ˢ y ⟩
        branch (inl⊎ qa) = inl⊎ (range-in a v z hv (fst data') ∣ q , qa , qp ∣₁)
        branch (inr⊎ eq) = inr⊎ (subst ⟨_⟩ (sym (paths z y))
          (snd (GS.ordered-components p v z x y
            (subst (λ t → ⟨ isKPairΔ t v z ⟩) (GS.≈→≡ eq) qp) hp)))

range-finite : (a : S) → ⟨ finiteIn PM.W a ⟩ → ⟨ finiteIn Y (range a) ⟩
range-finite a ha = subst ⟨_⟩ (rangeFinite-reading a)
  (finite-induction PM.W rangeFiniteFormula base step a ha)
  (range a) (range-witness a)
  where
  base : (e : S) → ⟨ emptyPred e ⟩ → ⟨ (e ∷ []) ⊨ rangeFiniteFormula ⟩
  base e he = subst ⟨_⟩ (sym (rangeFinite-reading e))
    (λ r hr → finite-empty Y r (λ z hz → PT.rec (snd ⊥)
      (λ { (v , hv , hp) → PT.rec (snd ⊥) (λ { (p , hpe , _) → he p hpe }) hp })
      (snd (fst (hr z) hz))))

  step : (a' b p : S) → ⟨ finiteIn PM.W a' ⟩
    → ⟨ (a' ∷ []) ⊨ rangeFiniteFormula ⟩
    → ⟨ p ∈ˢ PM.W ⟩ → ⟨ adjoinPred b a' p ⟩
    → ⟨ (b ∷ []) ⊨ rangeFiniteFormula ⟩
  step a' b p ha' ih hp hb = subst ⟨_⟩ (sym (rangeFinite-reading b))
    (λ r hr → subst (λ t → ⟨ finiteIn Y t ⟩) (sym (range-unique r b hr))
      (PT.rec (snd (finiteIn Y (range b)))
        (λ { (x , y , hx , hy , kp) →
          finite-adjoin Y (range b) (range a') y
            (subst ⟨_⟩ (rangeFinite-reading a') ih (range a') (range-witness a'))
            hy (range-adjoin b a' p x y hb hx hy kp) })
        (GS.product-out X Y p hp)))

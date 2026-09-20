{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile

module K8.FiniteUnion
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
open import FOL.Syntax using ( Formula; var; _∈̇_; _⇒̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
open import CodedVocabulary 𝒮 using ( sepAt; sepAt-reading )
open import CardinalBridge 𝒮 using ( _↔̇_ )
open import OrdinaryProfile 𝒮 using ( iff )
open import K8.FiniteVocabulary 𝒮 using ( finiteIn; finiteAt; emptyPred; adjoinPred )
open import K8.FiniteSets 𝒮 ext paths pow sep using ( finite-empty; finite-induction )
open import K8.FiniteOperations 𝒮 ext paths pair un pow sep seed using ( finite-join )
import K8.GroundSets
module GS = K8.GroundSets.Ground 𝒮 ext paths pair un pow sep seed
open import GroundDescription 𝒮 ext paths using ( the; the-spec; ext-path )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.Data.Sum using ( _⊎_ ) renaming ( inl to inl⊎; inr to inr⊎ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )
import Cubical.Data.Empty as Empty

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )

unionClass : S → S → Ω
unionClass A z = ⋁ S (λ b → (b ∈ˢ A) ⊓ (z ∈ˢ b))

opaque
  bigUnion : S → S
  bigUnion A = the (unionClass A) (un A)

  bigUnion-spec : (A z : S) → (z ∈ˢ bigUnion A) ≡ unionClass A z
  bigUnion-spec A = the-spec (unionClass A) (un A)

unionSpec : S → S → Ω
unionSpec u A = ⋀ S (λ z → iff (z ∈ˢ u) (unionClass A z))

unionSpecAt : Formula S 2
unionSpecAt = ∀̇ ((var zero ∈̇ var (suc zero)) ↔̇
  (∃̇∈ (var (suc (suc zero))) (var (suc zero) ∈̇ var zero)))

union-witness : (A : S) → ⟨ unionSpec (bigUnion A) A ⟩
union-witness A z = subst ⟨_⟩ (bigUnion-spec A z)
  , subst ⟨_⟩ (sym (bigUnion-spec A z))

union-unique : (u A : S) → ⟨ unionSpec u A ⟩ → u ≡ bigUnion A
union-unique u A h = ext-path (λ z → ⇔toPath (fst (h z)) (snd (h z))
  ∙ sym (bigUnion-spec A z))

union-adjoin : (B A b : S) → ⟨ adjoinPred B A b ⟩
  → bigUnion B ≡ GS.join (bigUnion A) b
union-adjoin B A b h = ext-path (λ z → bigUnion-spec B z
  ∙ ⇔toPath (forward z) (backward z)
  ∙ sym (GS.join-spec (bigUnion A) b z))
  where
  forward : (z : S) → ⟨ unionClass B z ⟩ → ⟨ (z ∈ˢ bigUnion A) ⊔ (z ∈ˢ b) ⟩
  forward z = PT.rec (snd ((z ∈ˢ bigUnion A) ⊔ (z ∈ˢ b)))
    (λ { (a , ha , hz) → PT.map
      (λ { (inl⊎ hA) → inl⊎ (subst ⟨_⟩ (sym (bigUnion-spec A z)) ∣ a , hA , hz ∣₁)
         ; (inr⊎ eq) → inr⊎ (subst (λ t → ⟨ z ∈ˢ t ⟩) (GS.≈→≡ eq) hz) })
      (snd (snd h) a ha) })

  backward : (z : S) → ⟨ (z ∈ˢ bigUnion A) ⊔ (z ∈ˢ b) ⟩ → ⟨ unionClass B z ⟩
  backward z = PT.rec (snd (unionClass B z))
    (λ { (inl⊎ hz) → PT.map (λ { (a , ha , za) → a , fst (snd h) a ha , za })
          (subst ⟨_⟩ (bigUnion-spec A z) hz)
       ; (inr⊎ hz) → ∣ b , fst h , hz ∣₁ })

finiteMembers : S → S → Ω
finiteMembers X A = ⋀ S (λ b → (b ∈ˢ A) ⇒ finiteIn X b)

unionFiniteAt : Formula S 2
unionFiniteAt = ∀̇ (
  (∀̇ ((var zero ∈̇ var (suc zero)) ↔̇
    (∃̇∈ (var (suc (suc zero))) (var (suc zero) ∈̇ var zero))))
  ⇒̇ ((∀̇∈ (var (suc zero)) (finiteAt (suc (suc (suc zero))) zero))
    ⇒̇ finiteAt (suc (suc zero)) zero))

unionFiniteFormula : S → Formula S 1
unionFiniteFormula X = sepAt unionFiniteAt (X ∷ [])

unionFinite-reading : (A X : S)
  → ((A ∷ []) ⊨ unionFiniteFormula X)
    ≡ (⋀ S (λ u → unionSpec u A ⇒ (finiteMembers X A ⇒ finiteIn X u)))
unionFinite-reading A X = sepAt-reading unionFiniteAt (X ∷ []) A

finite-bigUnion : (B X A : S) → ⟨ finiteIn B A ⟩ → ⟨ finiteMembers X A ⟩
  → ⟨ finiteIn X (bigUnion A) ⟩
finite-bigUnion B X A hA members = subst ⟨_⟩ (unionFinite-reading A X)
  (finite-induction B (unionFiniteFormula X) base step A hA)
  (bigUnion A) (union-witness A) members
  where
  base : (e : S) → ⟨ emptyPred e ⟩ → ⟨ (e ∷ []) ⊨ unionFiniteFormula X ⟩
  base e he = subst ⟨_⟩ (sym (unionFinite-reading e X))
    (λ u hu _ → finite-empty X u (λ z hz → PT.rec (snd ⊥)
      (λ { (b , hb , _) → he b hb }) (fst (hu z) hz)))

  step : (A' A'' b : S) → ⟨ finiteIn B A' ⟩
    → ⟨ (A' ∷ []) ⊨ unionFiniteFormula X ⟩
    → ⟨ b ∈ˢ B ⟩ → ⟨ adjoinPred A'' A' b ⟩
    → ⟨ (A'' ∷ []) ⊨ unionFiniteFormula X ⟩
  step A' A'' b hA' ih hb had = subst ⟨_⟩ (sym (unionFinite-reading A'' X))
    (λ u hu hm → subst (λ t → ⟨ finiteIn X t ⟩)
      (sym (union-unique u A'' hu ∙ union-adjoin A'' A' b had))
      (finite-join X (bigUnion A') b
        (subst ⟨_⟩ (unionFinite-reading A' X) ih (bigUnion A') (union-witness A')
          (λ a ha → hm a (fst (snd had) a ha)))
        (hm b (fst had))))

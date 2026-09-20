{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile

module K8.FiniteAmbient
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
    → ZFStructure._≈ˢ_ 𝒮 x y ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (sep : OrdinaryProfile.Separation 𝒮)
  where


open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; _⇒̇_; ∀̇_ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
open import CodedVocabulary 𝒮 using ( subsetΔ; subsetAtˢ )
open import K8.FiniteVocabulary 𝒮 using ( finiteIn; finiteAt; emptyPred; adjoinPred )
open import K8.FiniteSets 𝒮 ext paths pow sep
  using ( finite-empty; finite-adjoin; finite-induction )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )

ambientFormula : Formula S 1
ambientFormula = ∀̇ (subsetAtˢ (suc zero) zero ⇒̇ finiteAt zero (suc zero))

ambient-reading : (a : S) → ((a ∷ []) ⊨ ambientFormula)
  ≡ (⋀ S (λ Y → subsetΔ a Y ⇒ finiteIn Y a))
ambient-reading a = refl

finite-change-ambient : (X Y a : S) → ⟨ finiteIn X a ⟩
  → ⟨ subsetΔ a Y ⟩ → ⟨ finiteIn Y a ⟩
finite-change-ambient X Y a ha sub = subst ⟨_⟩ (ambient-reading a)
  (finite-induction X ambientFormula base step a ha) Y sub
  where
  base : (e : S) → ⟨ emptyPred e ⟩ → ⟨ (e ∷ []) ⊨ ambientFormula ⟩
  base e he = subst ⟨_⟩ (sym (ambient-reading e)) (λ Z _ → finite-empty Z e he)

  step : (a b x : S) → ⟨ finiteIn X a ⟩ → ⟨ (a ∷ []) ⊨ ambientFormula ⟩
    → ⟨ x ∈ˢ X ⟩ → ⟨ adjoinPred b a x ⟩ → ⟨ (b ∷ []) ⊨ ambientFormula ⟩
  step a b x ha ih hx hb = subst ⟨_⟩ (sym (ambient-reading b))
    (λ Z bs → finite-adjoin Z b a x
      (subst ⟨_⟩ (ambient-reading a) ih Z (λ z hz → bs z (fst (snd hb) z hz)))
      (bs x (fst hb)) hb)

finite-self : (X a : S) → ⟨ finiteIn X a ⟩ → ⟨ finiteIn a a ⟩
finite-self X a ha = finite-change-ambient X a a ha (λ z hz → hz)


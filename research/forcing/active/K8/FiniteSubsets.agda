{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile

module K8.FiniteSubsets
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
    → ZFStructure._≈ˢ_ 𝒮 x y ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (sep : OrdinaryProfile.Separation 𝒮)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _≐_; ¬̇_; _⇒̇_; ∀̇_ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
open import Base.Classical using ( LEM )
open import CodedVocabulary 𝒮 using ( subsetΔ; subsetAtˢ; sepAt; sepAt-reading )
open import K8.FiniteVocabulary 𝒮 using ( finiteIn; finiteAt; emptyPred; adjoinPred )
open import K8.FiniteSets 𝒮 ext paths pow sep
  using ( finite-empty; finite-adjoin; finite-induction )
open import GroundDescription 𝒮 ext paths using ( separateOf; separateOf-spec )
module OP = OrdinaryProfile 𝒮
open OP.PathRealization paths using ( ≈ˢ-to-path )
open import Cubical.Data.Sum using ( _⊎_ ) renaming ( inl to inl⊎; inr to inr⊎ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )
import Cubical.Data.Empty as Empty

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )

subsetFiniteAt : Formula S 2
subsetFiniteAt = ∀̇ (subsetAtˢ zero (suc zero) ⇒̇ finiteAt (suc (suc zero)) zero)

subsetFiniteFormula : S → Formula S 1
subsetFiniteFormula X = sepAt subsetFiniteAt (X ∷ [])

subsetFinite-reading : (a X : S)
  → ((a ∷ []) ⊨ subsetFiniteFormula X)
    ≡ (⋀ S (λ d → subsetΔ d a ⇒ finiteIn X d))
subsetFinite-reading a X = sepAt-reading subsetFiniteAt (X ∷ []) a

finite-subset : LEM ℓ → (X a d : S) → ⟨ finiteIn X a ⟩
  → ⟨ subsetΔ d a ⟩ → ⟨ finiteIn X d ⟩
finite-subset lem X a d ha sub = subst ⟨_⟩ (subsetFinite-reading a X)
  (finite-induction X (subsetFiniteFormula X) base step a ha) d sub
  where
  base : (e : S) → ⟨ emptyPred e ⟩ → ⟨ (e ∷ []) ⊨ subsetFiniteFormula X ⟩
  base e he = subst ⟨_⟩ (sym (subsetFinite-reading e X))
    (λ b hb → finite-empty X b (λ z hz → he z (hb z hz)))

  step : (a' b x : S) → ⟨ finiteIn X a' ⟩
    → ⟨ (a' ∷ []) ⊨ subsetFiniteFormula X ⟩
    → ⟨ x ∈ˢ X ⟩ → ⟨ adjoinPred b a' x ⟩
    → ⟨ (b ∷ []) ⊨ subsetFiniteFormula X ⟩
  step a' b x ha' ih hx hb = subst ⟨_⟩ (sym (subsetFinite-reading b X)) below
    where
    induction : (c : S) → ⟨ subsetΔ c a' ⟩ → ⟨ finiteIn X c ⟩
    induction = subst ⟨_⟩ (subsetFinite-reading a' X) ih

    below : (c : S) → ⟨ subsetΔ c b ⟩ → ⟨ finiteIn X c ⟩
    below c cb = choose (lem (x ∈ˢ c))
      where
      opaque
        cut : S
        cut = separateOf sep c (¬̇ (var zero ≐ con x))

        cut-spec : (z : S) → (z ∈ˢ cut) ≡ ((z ∈ˢ c) ⊓ ((z ≈ˢ x) ⇒ ⊥))
        cut-spec z = separateOf-spec sep c (¬̇ (var zero ≐ con x)) z

      cut-in : (z : S) → ⟨ z ∈ˢ c ⟩ → (⟨ z ≈ˢ x ⟩ → ⟨ ⊥ ⟩) → ⟨ z ∈ˢ cut ⟩
      cut-in z hz ne = subst ⟨_⟩ (sym (cut-spec z)) (hz , ne)

      cut-out : (z : S) → ⟨ z ∈ˢ cut ⟩ → ⟨ (z ∈ˢ c) ⊓ ((z ≈ˢ x) ⇒ ⊥) ⟩
      cut-out z = subst ⟨_⟩ (cut-spec z)

      cut-sub : ⟨ subsetΔ cut a' ⟩
      cut-sub z hz = PT.rec (snd (z ∈ˢ a'))
        (λ { (inl⊎ za) → za; (inr⊎ zx) → Empty.rec* (snd (cut-out z hz) zx) })
        (snd (snd hb) z (cb z (fst (cut-out z hz))))

      choose : ⟨ x ∈ˢ c ⟩ ⊎ (⟨ x ∈ˢ c ⟩ → Empty.⊥) → ⟨ finiteIn X c ⟩
      choose (inl⊎ xc) = finite-adjoin X c cut x (induction cut cut-sub) hx
        (xc , (λ z hz → fst (cut-out z hz)) , split)
        where
        split : (z : S) → ⟨ z ∈ˢ c ⟩ → ⟨ (z ∈ˢ cut) ⊔ (z ≈ˢ x) ⟩
        split z hz = case (lem (z ≈ˢ x))
          where
          case : ⟨ z ≈ˢ x ⟩ ⊎ (⟨ z ≈ˢ x ⟩ → Empty.⊥)
            → ⟨ (z ∈ˢ cut) ⊔ (z ≈ˢ x) ⟩
          case (inl⊎ eq) = ∣ inr⊎ eq ∣₁
          case (inr⊎ ne) = ∣ inl⊎ (cut-in z hz (λ eq → Empty.rec (ne eq))) ∣₁
      choose (inr⊎ nxc) = induction c (λ z hz → PT.rec (snd (z ∈ˢ a'))
        (λ { (inl⊎ za) → za
           ; (inr⊎ zx) → Empty.rec (nxc
               (subst (λ t → ⟨ t ∈ˢ c ⟩) (≈ˢ-to-path z x zx) hz)) })
        (snd (snd hb) z (cb z hz)))

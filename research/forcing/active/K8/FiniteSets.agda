{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile

module K8.FiniteSets
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
    → ZFStructure._≈ˢ_ 𝒮 x y ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (sep : OrdinaryProfile.Separation 𝒮)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; _∧̇_ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
open import CodedVocabulary 𝒮 using ( subsetΔ; sepAt; sepAt-reading )
open import K8.FiniteVocabulary 𝒮
  using ( finiteIn; finiteAt; emptyPred; adjoinPred; closedPred; finite-reading )
open import GroundDescription 𝒮 ext paths
  using ( powerOf; powerOf-spec; separateOf; separateOf-spec )
module OP = OrdinaryProfile 𝒮
open OP.PathRealization paths using ( ≈ˢ-to-path )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.Data.Sum using ( _⊎_ ) renaming ( inl to inl⊎; inr to inr⊎ )
import Cubical.HITs.PropositionalTruncation as PT
import Cubical.Data.Empty as Empty

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )

finite-empty : (X e : S) → ⟨ emptyPred e ⟩ → ⟨ finiteIn X e ⟩
finite-empty X e he = (λ z hz → Empty.rec* (he z hz))
  , (λ F hF → fst hF e he)

finite-adjoin : (X b a x : S) → ⟨ finiteIn X a ⟩ → ⟨ x ∈ˢ X ⟩
  → ⟨ adjoinPred b a x ⟩ → ⟨ finiteIn X b ⟩
finite-adjoin X b a x ha hx hb = sub ,
  (λ F hF → snd hF a (snd ha F hF) x hx b hb)
  where
  sub : ⟨ subsetΔ b X ⟩
  sub z hz = PT.rec (snd (z ∈ˢ X))
    (λ { (inl⊎ za) → fst ha z za
       ; (inr⊎ zx) → subst (λ u → ⟨ u ∈ˢ X ⟩)
           (sym (≈ˢ-to-path z x zx)) hx })
    (snd (snd hb) z hz)

finiteFormula : S → Formula S 1
finiteFormula X = sepAt (finiteAt (suc zero) zero) (X ∷ [])

finiteFormula-reading : (X a : S)
  → ((a ∷ []) ⊨ finiteFormula X) ≡ finiteIn X a
finiteFormula-reading X a =
  sepAt-reading (finiteAt (suc zero) zero) (X ∷ []) a
  ∙ finite-reading (suc zero) zero (a ∷ X ∷ [])

opaque
  finiteSubsets : S → S
  finiteSubsets X = separateOf sep (powerOf pow X) (finiteFormula X)

  finiteSubsets-spec : (X a : S)
    → (a ∈ˢ finiteSubsets X) ≡ finiteIn X a
  finiteSubsets-spec X a =
    separateOf-spec sep (powerOf pow X) (finiteFormula X) a
    ∙ cong₂ _⊓_ (powerOf-spec pow X a) (finiteFormula-reading X a)
    ∙ ⇔toPath snd (λ h → fst h , h)

finite-induction : (X : S) (φ : Formula S 1)
  → ((e : S) → ⟨ emptyPred e ⟩ → ⟨ (e ∷ []) ⊨ φ ⟩)
  → ((a b x : S) → ⟨ finiteIn X a ⟩ → ⟨ (a ∷ []) ⊨ φ ⟩
      → ⟨ x ∈ˢ X ⟩ → ⟨ adjoinPred b a x ⟩ → ⟨ (b ∷ []) ⊨ φ ⟩)
  → (a : S) → ⟨ finiteIn X a ⟩ → ⟨ (a ∷ []) ⊨ φ ⟩
finite-induction X φ base step a ha = snd (read a (snd ha family closed))
  where
  family : S
  family = separateOf sep (finiteSubsets X) φ

  spec : (b : S) → (b ∈ˢ family) ≡ (finiteIn X b ⊓ ((b ∷ []) ⊨ φ))
  spec b = separateOf-spec sep (finiteSubsets X) φ b
    ∙ cong (_⊓ ((b ∷ []) ⊨ φ)) (finiteSubsets-spec X b)

  read : (b : S) → ⟨ b ∈ˢ family ⟩ → ⟨ finiteIn X b ⊓ ((b ∷ []) ⊨ φ) ⟩
  read b = subst ⟨_⟩ (spec b)

  write : (b : S) → ⟨ finiteIn X b ⊓ ((b ∷ []) ⊨ φ) ⟩ → ⟨ b ∈ˢ family ⟩
  write b = subst ⟨_⟩ (sym (spec b))

  closed : ⟨ closedPred family X ⟩
  closed = (λ e he → write e (finite-empty X e he , base e he))
    , (λ u hu x hx b hb → write b
        ( finite-adjoin X b u x (fst (read u hu)) hx hb
        , step u b x (fst (read u hu)) (snd (read u hu)) hx hb ))

finite-ambient-mono : (X Y a : S) → ⟨ subsetΔ X Y ⟩
  → ⟨ finiteIn X a ⟩ → ⟨ finiteIn Y a ⟩
finite-ambient-mono X Y a sub ha = subst ⟨_⟩ (finiteFormula-reading Y a)
  (finite-induction X (finiteFormula Y)
    (λ e he → subst ⟨_⟩ (sym (finiteFormula-reading Y e)) (finite-empty Y e he))
    (λ u b x hu ih hx hb → subst ⟨_⟩ (sym (finiteFormula-reading Y b))
      (finite-adjoin Y b u x (subst ⟨_⟩ (finiteFormula-reading Y u) ih)
        (sub x hx) hb)) a ha)

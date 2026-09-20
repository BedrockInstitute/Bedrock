{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile

module K8.FamilyImages
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
  (seed : ZFStructure.S 𝒮)
  where


open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; con; ∃̇∈ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
open import OrdinaryProfile 𝒮 using ( ChoiceSet; module Swap )
open import CodedVocabulary 𝒮 using ( subsetΔ )
import K8.GroundSets
import K8.Uncountability
import CardinalBridge
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )

module GS = K8.GroundSets.Ground 𝒮 ext paths pair un pow sep seed
module UC = K8.Uncountability 𝒮 ext paths pair un pow sep coll find seed
module CB = CardinalBridge 𝒮

imagePred : S → Formula S 2 → S → Ω
imagePred I φ y = ⋁ S (λ x → (x ∈ˢ I) ⊓ ((y ∷ x ∷ []) ⊨ φ))

imageFormula : S → Formula S 2 → Formula S 1
imageFormula I φ = ∃̇∈ (con I) (Swap.swapFo φ)

image-reading : (I : S) (φ : Formula S 2) (y : S)
  → ((y ∷ []) ⊨ imageFormula I φ) ≡ imagePred I φ y
image-reading I φ y = cong (⋁ S)
  (funExt (λ x → cong ((x ∈ˢ I) ⊓_) (Swap.⊨-swap φ x y)))

opaque
  imageIn : S → S → Formula S 2 → S
  imageIn I Y φ = GS.separator Y (imageFormula I φ)

  image-spec : (I Y : S) (φ : Formula S 2) (y : S)
    → (y ∈ˢ imageIn I Y φ) ≡ ((y ∈ˢ Y) ⊓ imagePred I φ y)
  image-spec I Y φ y = GS.separator-spec Y (imageFormula I φ) y
    ∙ cong ((y ∈ˢ Y) ⊓_) (image-reading I φ y)

image-sub : (I Y : S) (φ : Formula S 2) → ⟨ subsetΔ (imageIn I Y φ) Y ⟩
image-sub I Y φ y hy = fst (subst ⟨_⟩ (image-spec I Y φ y) hy)

image-in : (I Y : S) (φ : Formula S 2) (x y : S)
  → ⟨ x ∈ˢ I ⟩ → ⟨ y ∈ˢ Y ⟩ → ⟨ (y ∷ x ∷ []) ⊨ φ ⟩
  → ⟨ y ∈ˢ imageIn I Y φ ⟩
image-in I Y φ x y hx hy sat = subst ⟨_⟩ (sym (image-spec I Y φ y))
  (hy , ∣ x , hx , sat ∣₁)

image-out : (I Y : S) (φ : Formula S 2) (y : S)
  → ⟨ y ∈ˢ imageIn I Y φ ⟩ → ⟨ imagePred I φ y ⟩
image-out I Y φ y hy = snd (subst ⟨_⟩ (image-spec I Y φ y) hy)

image-countable : ChoiceSet → (I Y w : S) → (φ : Formula S 2)
  → ((x y z : S) → ⟨ x ∈ˢ I ⟩ → ⟨ y ∈ˢ Y ⟩ → ⟨ z ∈ˢ Y ⟩
      → ⟨ (y ∷ x ∷ []) ⊨ φ ⟩ → ⟨ (z ∷ x ∷ []) ⊨ φ ⟩ → ⟨ y ≈ˢ z ⟩)
  → ⟨ CB.injectable I w ⟩ → ⟨ CB.injectable (imageIn I Y φ) w ⟩
image-countable choice I Y w φ single countI =
  UC.countable-image choice I (imageIn I Y φ) w φ (image-out I Y φ)
    (λ x y z hx hy hz → single x y z hx
      (image-sub I Y φ y hy) (image-sub I Y φ z hz)) countI


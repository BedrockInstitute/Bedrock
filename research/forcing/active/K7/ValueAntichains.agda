{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile

module K7.ValueAntichains
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
open import FOL.Syntax using ( Formula; var; con )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
open import Base.Classical using ( LEM )
open import OrdinaryProfile 𝒮 using ( ChoiceSet )
open import CodedVocabulary 𝒮 using ( subsetΔ; compatibleΔ )
open import Cubical.Data.Sum using ( inl; inr )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )
import CardinalBridge
import K7.ChainConditions
import K8.CountableUnion
import K8.FamilyImages
import K8.GroundSets

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )

module CB = CardinalBridge 𝒮
module CA = K7.ChainConditions 𝒮 ext paths
module CU = K8.CountableUnion 𝒮 ext paths pair un pow sep coll find seed
module FI = K8.FamilyImages 𝒮 ext paths pair un pow sep coll find seed
module GS = K8.GroundSets.Ground 𝒮 ext paths pair un pow sep seed

-- The relation has environment (condition, value). Ground ChoiceSet selects
-- one condition for each value by a set graph, and Separation takes its range.
-- Determinacy makes this graph injective. Incompatibility for distinct values
-- makes its range an antichain, because the selected graph is single-valued.
-- The forcing-specific proofs of these relation properties remain separate.

module AtRelation
  (lem : LEM ℓ) (choice : ChoiceSet) (V c o : S) (φ : Formula S 2)
  (total : (a : S) → ⟨ a ∈ˢ V ⟩
    → ⟨ ⋁ S (λ p → (p ∈ˢ c) ⊓ ((p ∷ a ∷ []) ⊨ φ)) ⟩)
  (determinate : (a b p : S) → ⟨ a ∈ˢ V ⟩ → ⟨ b ∈ˢ V ⟩ → ⟨ p ∈ˢ c ⟩
    → ⟨ (p ∷ a ∷ []) ⊨ φ ⟩ → ⟨ (p ∷ b ∷ []) ⊨ φ ⟩ → ⟨ a ≈ˢ b ⟩)
  (incompatible : (a b p q : S)
    → ⟨ a ∈ˢ V ⟩ → ⟨ b ∈ˢ V ⟩ → ⟨ p ∈ˢ c ⟩ → ⟨ q ∈ˢ c ⟩
    → ⟨ (p ∷ a ∷ []) ⊨ φ ⟩ → ⟨ (q ∷ b ∷ []) ⊨ φ ⟩
    → (⟨ a ≈ˢ b ⟩ → Empty.⊥) → ⟨ compatibleΔ c o p q ⟩ → Empty.⊥)
  where

  module AtSelection (g : S) (hg : ⟨ CU.Selection V c φ g ⟩) where

    graphFormula : Formula S 2
    graphFormula = CU.refAt (con g) (var (suc zero)) (var zero)

    graph-reading : (p a : S)
      → ((p ∷ a ∷ []) ⊨ graphFormula) ≡ CU.Ref g a p
    graph-reading p a = CU.refAt-reading (con g) (var (suc zero))
      (var zero) (p ∷ a ∷ [])

    d : S
    d = FI.imageIn V c graphFormula

    range-in : (a p : S) → ⟨ a ∈ˢ V ⟩ → ⟨ p ∈ˢ c ⟩
      → ⟨ CU.Ref g a p ⟩ → ⟨ p ∈ˢ d ⟩
    range-in a p ha hp h = FI.image-in V c graphFormula a p ha hp
      (subst ⟨_⟩ (sym (graph-reading p a)) h)

    range-out : (p : S) → ⟨ p ∈ˢ d ⟩
      → ⟨ ⋁ S (λ a → (a ∈ˢ V) ⊓ CU.Ref g a p) ⟩
    range-out p hp = PT.map
      (λ { (a , ha , h) → a , ha , subst ⟨_⟩ (graph-reading p a) h })
      (FI.image-out V c graphFormula p hp)

    range-subset : ⟨ subsetΔ d c ⟩
    range-subset = FI.image-sub V c graphFormula

    graph-injection : ⟨ CB.isInjection g V d ⟩
    graph-injection = hg .fst , hg .snd .fst
      , (λ z hz a p kp → range-in a p
          (hg .snd .snd z hz a p kp .fst)
          (hg .snd .snd z hz a p kp .snd .fst) ∣ z , hz , kp ∣₁)
      , λ z hz t ht a p b (kp , kq) → determinate a b p
          (hg .snd .snd z hz a p kp .fst)
          (hg .snd .snd t ht b p kq .fst)
          (hg .snd .snd z hz a p kp .snd .fst)
          (hg .snd .snd z hz a p kp .snd .snd)
          (hg .snd .snd t ht b p kq .snd .snd)

    selected-compatible : (a b p q : S)
      → ⟨ a ∈ˢ V ⟩ → ⟨ b ∈ˢ V ⟩ → ⟨ p ∈ˢ c ⟩ → ⟨ q ∈ˢ c ⟩
      → ⟨ CU.Ref g a p ⟩ → ⟨ CU.Ref g b q ⟩
      → ⟨ compatibleΔ c o p q ⟩ → ⟨ p ≈ˢ q ⟩
    selected-compatible a b p q ha hb hp hq h k comp with lem (a ≈ˢ b)
    ... | inl eq = CU.ref-single g a p q (hg .fst) h
      (subst (λ x → ⟨ CU.Ref g x q ⟩) (sym (GS.≈→≡ eq)) k)
    ... | inr neq = Empty.rec (incompatible a b p q ha hb hp hq
      (CU.selection-value V c φ g a p hg h .snd .snd)
      (CU.selection-value V c φ g b q hg k .snd .snd) neq comp)

    range-antichain : ⟨ CA.antichainΔ c o d ⟩
    range-antichain = CA.antichain-intro c o d
      (λ p q hp hd hq he comp → PT.rec (snd (p ≈ˢ q))
        (λ { (a , ha , h) → PT.rec (snd (p ≈ˢ q))
          (λ { (b , hb , k) → selected-compatible a b p q ha hb hp hq h k comp })
          (range-out q he) }) (range-out p hd))

  selected-antichain : ⟨ ⋁ S (λ d → (subsetΔ d c ⊓ CA.antichainΔ c o d)
    ⊓ CB.injectable V d) ⟩
  selected-antichain = PT.map
    (λ { (g , hg) → AtSelection.d g hg
      , (AtSelection.range-subset g hg , AtSelection.range-antichain g hg)
      , ∣ g , AtSelection.graph-injection g hg ∣₁ })
    (CU.bounded-choice choice V c φ total)

{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile

module K8.FullDeltaSystem
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
open import OrdinaryProfile 𝒮 using ( ChoiceSet )
open import K8.FiniteVocabulary 𝒮 using ( finiteIn )
open import CodedVocabulary 𝒮 using ( subsetΔ )
import CardinalBridge
import K8.DeltaSystem
import K8.CountableComponents
import K8.ComponentRepresentatives
import K8.CountableStars
import K8.DisjointFamilies
import K8.Uncountability

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
module CB = CardinalBridge 𝒮 using ( isOmega; injectable )
module UC = K8.Uncountability 𝒮 ext paths pair un pow sep coll find seed using ( uncountable )
module CS = K8.CountableStars 𝒮 ext paths pair un pow sep coll find seed using ( module Family )
module DJ = K8.DisjointFamilies 𝒮 ext paths pair un pow sep seed using ( pairwiseDisjoint )

module AtOmega (lem : LEM ℓ) (choice : ChoiceSet) (w : S) (hw : ⟨ CB.isOmega w ⟩) where
  module DS = K8.DeltaSystem.AtOmega 𝒮 ext paths pair un pow sep coll find seed lem choice w hw
    using ( Delta; Result )
  open DS public using ( Delta; Result )

  disjoint-uncountable : (F X : S)
    → ((a : S) → ⟨ a ∈ˢ F ⟩ → ⟨ finiteIn X a ⟩)
    → ⟨ UC.uncountable w F ⟩
    → ((x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ CB.injectable (CS.Family.star F X x) w ⟩)
    → ⟨ ⋁ S (λ B → subsetΔ B F ⊓ (UC.uncountable w B ⊓ DJ.pairwiseDisjoint B)) ⟩
  disjoint-uncountable F X each unF stars = Reps.disjoint-uncountable unF
    where
    module Components = K8.CountableComponents.Family 𝒮 ext paths pair un pow sep coll find seed
      lem choice w hw F X each using ( component-countable )
    module Reps = K8.ComponentRepresentatives.AtOmega.Family 𝒮 ext paths pair un pow sep coll find seed
      lem choice w hw F X (Components.component-countable stars) using ( disjoint-uncountable )

  finite-delta : (X F : S)
    → ((a : S) → ⟨ a ∈ˢ F ⟩ → ⟨ finiteIn X a ⟩)
    → ⟨ UC.uncountable w F ⟩ → ⟨ Result F ⟩
  finite-delta X = K8.DeltaSystem.AtOmega.WithDisjoint.finite-delta
    𝒮 ext paths pair un pow sep coll find seed lem choice w hw disjoint-uncountable X

  finite-delta-with-root : (X F : S)
    → ((a : S) → ⟨ a ∈ˢ F ⟩ → ⟨ finiteIn X a ⟩)
    → ⟨ UC.uncountable w F ⟩
    → ⟨ ⋁ S (λ B → subsetΔ B F ⊓ (UC.uncountable w B ⊓
        ⋁ S (λ r → finiteIn X r ⊓ Delta B r))) ⟩
  finite-delta-with-root X = K8.DeltaSystem.AtOmega.WithDisjoint.finite-delta-with-root
    𝒮 ext paths pair un pow sep coll find seed lem choice w hw disjoint-uncountable X

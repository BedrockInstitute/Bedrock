{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )

module K10.PreservationBoundary {ℓ}
  (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (paths : (x y : ZFStructure.S 𝒮)
         → (ZFStructure._≈ˢ_ 𝒮 x y)
         ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  where

open import FOL.ZFStructure using ( module hPropStructure )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
import OrdinaryProfile
import CardinalBridge
import CodedVocabulary
import K7.ChainConditions

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

module OP = OrdinaryProfile 𝒮
module CB = CardinalBridge 𝒮
module CV = CodedVocabulary 𝒮
open OP.PathRealization paths using ( ≈ˢ-to-path )

module Boundary
  (ext : OP.Extensionality)
  (Nm : Type ℓ)
  (valuesOf : OP.Separation → Nm → S → S)
  (c o w κ : S)
  (injectable-trans : OP.Separation → OP.Collection → (a b d : S)
                    → ⟨ CB.injectable a b ⟩ → ⟨ CB.injectable b d ⟩
                    → ⟨ CB.injectable a d ⟩)
  where

  module CA = K7.ChainConditions 𝒮 ext paths

  -- This is the rejected schema from the immutable K10 partial checkpoint,
  -- before the local-condition repair. The repaired K7.NoCollapse schema
  -- instead requires a common condition and forced functionality.
  RejectedValueAntichain : Type ℓ
  RejectedValueAntichain =
    (sep : OP.Separation) (f : Nm) (ξ : S)
    → ⟨ ⋁ S (λ d → ((CV.subsetΔ d c) ⊓ CA.antichainΔ c o d)
         ⊓ CB.injectable (valuesOf sep f ξ) d) ⟩

  -- A witness that the possible values at one coordinate fill κ.
  FullPossibleValues : OP.Separation → Nm → S → Type ℓ
  FullPossibleValues sep f ξ =
    ⟨ ⋀ S (λ a → OP.iff (a ∈ˢ valuesOf sep f ξ) (a ∈ˢ κ)) ⟩

  schema-counts-all-values : RejectedValueAntichain → OP.Collection
                           → (sep : OP.Separation) (f : Nm) (ξ : S)
                           → ⟨ CA.CCC₂ᴵ c o w ⟩
                           → ⟨ CB.injectable (valuesOf sep f ξ) w ⟩
  schema-counts-all-values va coll sep f ξ hccc =
    PT.rec (snd (CB.injectable (valuesOf sep f ξ) w))
      (λ { (d , (hsub , hac) , hinj) →
           injectable-trans sep coll (valuesOf sep f ξ) d w hinj
             (CA.ccc-use c o w d hccc hsub hac) })
      (va sep f ξ)

  schema-refuted-by-full-values : RejectedValueAntichain → OP.Collection
                                → (sep : OP.Separation) (f : Nm) (ξ : S)
                                → ⟨ CA.CCC₂ᴵ c o w ⟩
                                → FullPossibleValues sep f ξ
                                → (⟨ CB.injectable κ w ⟩ → Empty.⊥)
                                → Empty.⊥
  schema-refuted-by-full-values va coll sep f ξ hccc full uncountable =
    uncountable
      (subst (λ x → ⟨ CB.injectable x w ⟩) values-path
        (schema-counts-all-values va coll sep f ξ hccc))
    where
      values-path : valuesOf sep f ξ ≡ κ
      values-path = ≈ˢ-to-path (valuesOf sep f ξ) κ
        (ext (valuesOf sep f ξ) κ full)

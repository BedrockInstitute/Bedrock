{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile

module K8.RecursionInduction
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
open import FOL.Syntax using ( Formula; var; con; _⇒̇_; ∀̇∈ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
open import FOL.Manipulation.Renaming using ( renameFo; module Sat )
open import K8.FiniteVocabulary 𝒮 using ( emptyPred )
open import CodedVocabulary 𝒮 using ( refinesΔ )
import K8.GroundSets
import K8.OmegaRecursion
import K8.OmegaInduction
import K8.OmegaSuccessor
import K8.CountableUnion
import CardinalBridge
import Cubical.HITs.PropositionalTruncation as PT

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )
module GS = K8.GroundSets.Ground 𝒮 ext paths pair un pow sep seed
module OI = K8.OmegaInduction 𝒮 ext paths pair un pow sep seed
module OS = K8.OmegaSuccessor 𝒮 ext paths pair un pow sep find seed
module CU = K8.CountableUnion 𝒮 ext paths pair un pow sep coll find seed
module OR = K8.OmegaRecursion 𝒮 ext paths pair un pow sep coll find seed
module CB = CardinalBridge 𝒮
module Ren = Sat (hPropAlgebra ℓ) 𝒮 id

module AtOmega (lem : LEM ℓ) (w : S) (hw : ⟨ CB.isOmega w ⟩)
  (Y t a : S) (ha : ⟨ a ∈ˢ Y ⟩)
  (tf : ⟨ CB.isFunction t ⟩)
  (tt : (u : S) → ⟨ u ∈ˢ Y ⟩ → ⟨ ⋁ S (λ v → (v ∈ˢ Y) ⊓ CU.Ref t u v) ⟩)
  where
  module R = OR.AtOmega lem w hw Y t a ha tf tt

  module Invariant (φ : Formula S 1)
    (base : ⟨ (a ∷ []) ⊨ φ ⟩)
    (step : (u v : S) → ⟨ u ∈ˢ Y ⟩ → ⟨ v ∈ˢ Y ⟩ → ⟨ CU.Ref t u v ⟩
      → ⟨ (u ∷ []) ⊨ φ ⟩ → ⟨ (v ∷ []) ⊨ φ ⟩)
    where
    motive : Formula S 1
    motive = ∀̇∈ (con Y) (OR.deltaAt (con R.recursion) (var (suc zero)) (var zero)
      ⇒̇ renameFo (λ _ → zero) φ)

    Inv : S → Ω
    Inv n = ⋀ S (λ v → (v ∈ˢ Y) ⇒
      (refinesΔ R.recursion n v ⇒ ((v ∷ []) ⊨ φ)))

    reading : (n : S) → ((n ∷ []) ⊨ motive) ≡ Inv n
    reading n = cong (⋀ S) (funExt λ v → cong ((v ∈ˢ Y) ⇒_)
      (cong (refinesΔ R.recursion n v ⇒_)
        (Ren.⊨-rename (λ _ → zero) φ (v ∷ n ∷ []) (v ∷ []) (λ { zero → refl }))))

    zero-case : (e : S) → ⟨ e ∈ˢ w ⟩ → ⟨ emptyPred e ⟩ → ⟨ Inv e ⟩
    zero-case e he ee v hv ev = subst (λ z → ⟨ (z ∷ []) ⊨ φ ⟩)
      (GS.≈→≡ (CU.ref-single R.recursion OS.zeroSet a v R.recursion-function
        R.recursion-zero (subst (λ z → ⟨ CU.Ref R.recursion z v ⟩)
          (OS.empty-unique e ee) (OR.coded-ref R.recursion e v ev)))) base

    succ-case : (n s : S) → ⟨ n ∈ˢ w ⟩ → ⟨ Inv n ⟩
      → ⟨ s ∈ˢ w ⟩ → ⟨ CB.isSuccOf s n ⟩ → ⟨ Inv s ⟩
    succ-case n s hn ih hs sn v hv sv = PT.rec (snd ((v ∷ []) ⊨ φ))
      (λ { (u , hu , nu) → step u v hu hv
        (R.recursion-step n u v hn nu
          (subst (λ z → ⟨ CU.Ref R.recursion z v ⟩)
            (OS.successor-unique s n sn) (OR.coded-ref R.recursion s v sv)))
        (ih u hu (OR.delta-ref R.recursion n u nu)) }) (R.recursion-total n hn)

    holds : (n v : S) → ⟨ n ∈ˢ w ⟩ → ⟨ CU.Ref R.recursion n v ⟩
      → ⟨ (v ∷ []) ⊨ φ ⟩
    holds n v hn nv = subst ⟨_⟩ (reading n)
      (OI.omega-induction w hw motive
        (λ e he ee → subst ⟨_⟩ (sym (reading e)) (zero-case e he ee))
        (λ k s hk ih hs sk → subst ⟨_⟩ (sym (reading s))
          (succ-case k s hk (subst ⟨_⟩ (reading k) ih) hs sk)) n hn)
      v (R.recursion-typed n v nv .snd) (OR.delta-ref R.recursion n v nv)

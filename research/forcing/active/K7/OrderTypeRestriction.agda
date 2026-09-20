{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile

module K7.OrderTypeRestriction
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
    → ZFStructure._≈ˢ_ 𝒮 x y ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  (pair : OrdinaryProfile.Pairing 𝒮) (un : OrdinaryProfile.Union 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮) (sep : OrdinaryProfile.Separation 𝒮)
  (coll : OrdinaryProfile.Collection 𝒮)
  (find : OrdinaryProfile.FoundationInduction 𝒮)
  (seed : ZFStructure.S 𝒮)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _∈̇_; _⇒̇_ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.Data.Sum using ( inl; inr )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
import CardinalBridge
import K7.OrderTypeUniqueness
import K8.FinitePigeonhole

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )
open PT using ( ∣_∣₁ )

module Cardinal = CardinalBridge 𝒮
module Uniqueness = K7.OrderTypeUniqueness 𝒮 ext paths find
module Product = K8.FinitePigeonhole 𝒮 ext paths pair un pow sep coll find seed
module Ground = Product.GS
module Order = Product.CO
module Union = Product.CU
open Uniqueness using ( Ref; refAt; refAt-reading; isOrderIso; ≈→≡ )

opaque
  predecessors : S → S → S → S
  predecessors A r q = Ground.separator A (refAt (con r) (var zero) (con q))

  predecessors-reading : (A r q x : S)
    → (x ∈ˢ predecessors A r q) ≡ ((x ∈ˢ A) ⊓ Ref r x q)
  predecessors-reading A r q x = Ground.separator-spec A
    (refAt (con r) (var zero) (con q)) x
    ∙ cong ((x ∈ˢ A) ⊓_) (refAt-reading (con r) (var zero) (con q) (x ∷ []))

ordinal-members : (b : S) → ⟨ Cardinal.isOrdinal b ⟩
  → (a : S) → ⟨ a ∈ˢ b ⟩ → ⟨ Cardinal.isOrdinal a ⟩
ordinal-members b ob = find motive step
  where
  motive : Formula S 1
  motive = (var zero ∈̇ con b) ⇒̇ Cardinal.IsOrdinalφ

  step : (x : S) → ((y : S) → ⟨ y ∈ˢ x ⟩ → ⟨ (y ∷ []) ⊨ motive ⟩)
    → ⟨ (x ∷ []) ⊨ motive ⟩
  step x ih hx = transitive , linear
    where
    transitive : (y : S) → ⟨ y ∈ˢ x ⟩ → (z : S) → ⟨ z ∈ˢ y ⟩ → ⟨ z ∈ˢ x ⟩
    transitive y hy z hz = PT.rec (snd (z ∈ˢ x))
      (λ { (inl zx) → zx
         ; (inr h) → PT.rec (snd (z ∈ˢ x))
           (λ { (inl eq) → impossible (subst (λ t → ⟨ t ∈ˢ y ⟩) (≈→≡ z x eq) hz)
              ; (inr xz) → impossible (oy .fst z hz x xz) }) h })
      (ob .snd z (ob .fst y (ob .fst x hx y hy) z hz) x hx)
      where
      oy : ⟨ Cardinal.isOrdinal y ⟩
      oy = ih y hy (ob .fst x hx y hy)
      impossible : ⟨ x ∈ˢ y ⟩ → ⟨ z ∈ˢ x ⟩
      impossible xy = Empty.rec (Order.no-self find y (oy .fst x xy y hy))

    linear : (a : S) → ⟨ a ∈ˢ x ⟩ → (c : S) → ⟨ c ∈ˢ x ⟩
      → ⟨ (a ∈ˢ c) ⊔ ((a ≈ˢ c) ⊔ (c ∈ˢ a)) ⟩
    linear a ha c hc = ob .snd a (ob .fst x hx a ha) c (ob .fst x hx c hc)

module AtPreimage (f b A r c q : S)
  (ob : ⟨ Cardinal.isOrdinal b ⟩)
  (hf : ⟨ isOrderIso f b A r ⟩)
  (hc : ⟨ c ∈ˢ b ⟩)
  (fq : ⟨ Ref f c q ⟩)
  where

  formula : Formula S 2
  formula = refAt (con f) (var (suc zero)) (var zero)

  reading : (v u : S) → ((v ∷ u ∷ []) ⊨ formula) ≡ Ref f u v
  reading v u = refAt-reading (con f) (var (suc zero)) (var zero) (v ∷ u ∷ [])

  module Graph = Product.Graph c (predecessors A r q) formula

  graph : S
  graph = Graph.graph

  graph-reading : (x y : S)
    → Ref graph x y ≡ ((x ∈ˢ c) ⊓ ((y ∈ˢ predecessors A r q) ⊓ Ref f x y))
  graph-reading x y = ⇔toPath (Graph.ref-entry x y)
    (λ h → Graph.ref-in x y (h .fst) (h .snd .fst) (h .snd .snd))
    ∙ cong ((x ∈ˢ c) ⊓_) (cong ((y ∈ˢ predecessors A r q) ⊓_) (reading y x))

  total : (x : S) → ⟨ x ∈ˢ c ⟩
    → ⟨ ⋁ S (λ y → (y ∈ˢ predecessors A r q) ⊓ Graph.R y x) ⟩
  total x hx = PT.map (λ { (y , fy) → y ,
    subst ⟨_⟩ (sym (predecessors-reading A r q y))
      (Uniqueness.ref-range f b A r x y hf fy ,
        hf .snd .snd .snd x (ob .fst c hc x hx) c hc y q (fy , fq) .fst hx)
    , subst ⟨_⟩ (sym (reading y x)) fy })
    (hf .fst .snd .fst x (ob .fst c hc x hx))

  injection : ⟨ Cardinal.isInjection graph c (predecessors A r q) ⟩
  injection = Graph.injection total
    (λ x y z h k → Uniqueness.ref-single f b A r x y z hf
      (subst ⟨_⟩ (reading y x) h) (subst ⟨_⟩ (reading z x) k))
    (λ x y z h k → Union.ref-injective f b A x y z (hf .fst)
      (subst ⟨_⟩ (reading y x) h) (subst ⟨_⟩ (reading y z) k))

  onto : ⟨ Uniqueness.Onto graph c (predecessors A r q) ⟩
  onto y hy = PT.map (λ { (x , hx , fy) → x ,
    hf .snd .snd .snd x hx c hc y q (fy , fq) .snd atq
    , Graph.ref-in x y (hf .snd .snd .snd x hx c hc y q (fy , fq) .snd atq) hy
      (subst ⟨_⟩ (sym (reading y x)) fy) })
    (hf .snd .snd .fst y (subst ⟨_⟩ (predecessors-reading A r q y) hy .fst))
    where
    atq : ⟨ Ref r y q ⟩
    atq = subst ⟨_⟩ (predecessors-reading A r q y) hy .snd

  preserves : ⟨ Uniqueness.Preserves graph c r ⟩
  preserves x hx y hy u v (gx , gy) =
    hf .snd .snd .snd x (ob .fst c hc x hx) y (ob .fst c hc y hy) u v
      (subst ⟨_⟩ (graph-reading x u) gx .snd .snd ,
        subst ⟨_⟩ (graph-reading y v) gy .snd .snd)

  restriction-isomorphism : ⟨ isOrderIso graph c (predecessors A r q) r ⟩
  restriction-isomorphism = Uniqueness.order-isomorphism graph c (predecessors A r q) r
    injection onto preserves

  restriction-ordinal : ⟨ Cardinal.isOrdinal c ⟩
  restriction-ordinal = ordinal-members b ob c hc

  proper-initial-type : (a g : S) → ⟨ Cardinal.isOrdinal a ⟩
    → ⟨ isOrderIso g a (predecessors A r q) r ⟩ → ⟨ a ∈ˢ b ⟩
  proper-initial-type a g oa hg = subst (λ t → ⟨ t ∈ˢ b ⟩)
    (sym (≈→≡ a c (Uniqueness.order-isomorphism-unique g graph a c
      (predecessors A r q) r oa restriction-ordinal hg restriction-isomorphism .fst))) hc

proper-initial-comparison : (f b A r q a g : S)
  → ⟨ Cardinal.isOrdinal b ⟩ → ⟨ isOrderIso f b A r ⟩ → ⟨ q ∈ˢ A ⟩
  → ⟨ Cardinal.isOrdinal a ⟩ → ⟨ isOrderIso g a (predecessors A r q) r ⟩
  → ⟨ a ∈ˢ b ⟩
proper-initial-comparison f b A r q a g ob hf hq oa hg = PT.rec (snd (a ∈ˢ b))
  (λ { (c , hc , fq) → AtPreimage.proper-initial-type f b A r c q ob hf hc fq a g oa hg })
  (hf .snd .snd .fst q hq)

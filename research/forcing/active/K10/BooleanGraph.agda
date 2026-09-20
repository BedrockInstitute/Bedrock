{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile

module K10.BooleanGraph
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (families : NameKernel.Families 𝒮)
  (accessible : NameKernel.Accessibility 𝒮)
  (images : NameKernel.MemberImage 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (κ w : ZFStructure.S 𝒮)
  (lem : LEM ℓ)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.HITs.PropositionalTruncation as PT
import Cubical.Data.Empty as Empty
import CardinalBridge
import K4.Algebra
import K4.Implication
import K5.Frame
import K9.BooleanNameGround
import K9.BooleanReals
import K9.BooleanSeparation
import K9.GraphNames
import K9.IndexedNames
import K9.RealNames
import K10.BooleanPairs

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open PT using ( ∥_∥₁; ∣_∣₁ )
module BG = K9.BooleanNameGround 𝒮 families accessible images pow κ w lem
  using ( B; weight; weight-upper; entry-agrees; translated-check
        ; translated-check-distinct; module NG; module IC; module BK; module Atomic
        ; module Laws; module Translation; module BSupport; module Base )
module Graph = K9.GraphNames 𝒮 families accessible images pow κ w
  using ( graph; graphCode; vertex )
module Indexed = K9.IndexedNames 𝒮 families accessible images pow κ w
  using ( indexed-spec; indexed-entry )
module Reals = K9.BooleanReals 𝒮 families accessible images pow κ w lem
  using ( realB; module DenseDistinct )
module SourceReals = K9.RealNames 𝒮 families accessible images pow κ w using ( realCode )
module Pairs = K10.BooleanPairs 𝒮 families accessible images pow κ w lem
  using ( singleB; pairB; orderedB; singleB-member-value; pairB-member-value; orderedB-member-value )
open BG.NG using ( extensional; ≈ˢ-paths )
open K4.Algebra 𝒮 using ( Pt; Pt≡; _≤ᴮ_; ≤ᴮ-refl; ⊆ˢ-trans )
open K4.Algebra.Lattice BG.IC.codedLattice
open K4.Algebra.Complement BG.IC.codedComplement using ( ¬ᴮ_ )
open K4.Implication 𝒮 extensional ≈ˢ-paths BG.B BG.IC.codedLattice BG.IC.codedComplement
  using ( ≤ᴮ-antisym; ⊓-⊤; ⊓-comm; ≤-both-⊥ )
open BG.Atomic using () renaming ( _≈ᴮ_ to eq; _∈ᴮ_ to mem )
module FP = K5.Frame.Poset 𝒮 BG.NG.C.carrier BG.NG.C.order
module FF = FP.Forcing extensional ≈ˢ-paths BG.B BG.IC.codedLattice BG.IC.codedComplement BG.IC.codedComplete
  (BG.Base.codedBase lem) using ( _⊩ᴮ_; ⊩ᴮ-intro )
open FP using ( Cond )
open K5.Frame.Poset.ForcingBase (BG.Base.codedBase lem) using ( i )
module Separation = K9.BooleanSeparation 𝒮 extensional ≈ˢ-paths
  BG.NG.C.carrier BG.NG.C.order BG.B BG.IC.codedLattice BG.IC.codedComplement BG.IC.codedComplete
  (BG.Base.codedBase lem) using ( all-force-top )

private
  ≈→≡ : {a b : S} → ⟨ a ≈ˢ b ⟩ → a ≡ b
  ≈→≡ {a} {b} = subst ⟨_⟩ (≈ˢ-paths a b)

  ≈-refl : (a : S) → ⟨ a ≈ˢ a ⟩
  ≈-refl a = subst ⟨_⟩ (sym (≈ˢ-paths a a)) refl

graphB : S
graphB = BG.Translation.trᴮ Graph.graphCode

vertexB : S → S
vertexB α = BG.Translation.trᴮ (fst (Graph.vertex α))

vertexB-pair : (α : S)
  → vertexB α ≡ Pairs.orderedB (BG.NG.Check.chk α) (SourceReals.realCode α)
vertexB-pair α = refl

vertexB-member-value : (α z : S)
  → mem z (vertexB α) ≡
    (eq z (Pairs.singleB (BG.NG.Check.chk α))
      ⊔ᴮ eq z (Pairs.pairB (BG.NG.Check.chk α) (SourceReals.realCode α)))
vertexB-member-value α z = Pairs.orderedB-member-value (BG.NG.Check.chk α) (SourceReals.realCode α) z

vertexB-singleton-value : (α z : S)
  → mem z (Pairs.singleB (BG.NG.Check.chk α)) ≡ eq z (BG.translated-check α)
vertexB-singleton-value α z = Pairs.singleB-member-value (BG.NG.Check.chk α) z

vertexB-doubleton-value : (α z : S)
  → mem z (Pairs.pairB (BG.NG.Check.chk α) (SourceReals.realCode α))
    ≡ (eq z (BG.translated-check α) ⊔ᴮ eq z (Reals.realB α))
vertexB-doubleton-value α z = Pairs.pairB-member-value (BG.NG.Check.chk α) (SourceReals.realCode α) z

graphB-name : ⟨ BG.BK.IsName graphB ⟩
graphB-name = BG.Translation.trᴮ-name Graph.graphCode (snd Graph.graph)

vertexB-name : (α : S) → ⟨ BG.BK.IsName (vertexB α) ⟩
vertexB-name α = BG.Translation.trᴮ-name (fst (Graph.vertex α)) (snd (Graph.vertex α))

graphB-entry : (α : S) → ⟨ α ∈ˢ κ ⟩ → (p : Cond)
  → ⟨ BG.BK.entry (vertexB α) (fst (i p)) ∈ˢ graphB ⟩
graphB-entry α hα p = subst ⟨_⟩ (sym (BG.Translation.trᴮ-entries Graph.graphCode _))
  ∣ fst (Graph.vertex α) , ∣ fst p , ∣ snd p , source ,
    ≈-refl (BG.BK.entry (vertexB α) (fst (i p))) ∣₁ ∣₁ ∣₁
  where
  source : ⟨ BG.BK.entry (fst (Graph.vertex α)) (fst p) ∈ˢ Graph.graphCode ⟩
  source = subst (λ e → ⟨ e ∈ˢ Graph.graphCode ⟩)
    (sym (BG.entry-agrees (fst (Graph.vertex α)) (fst p)))
    (Indexed.indexed-entry κ (λ a → fst (Graph.vertex a)) α (fst p) hα (snd p))

EntryIndex : S → Pt BG.B → Type ℓ
EntryIndex x b = ∥ Σ[ α ∈ S ] (⟨ α ∈ˢ κ ⟩ × (Σ[ p ∈ Cond ]
  ((x ≡ vertexB α) × (b ≡ i p)))) ∥₁

graphB-entry-out : (x : S) (b : Pt BG.B)
  → ⟨ BG.BK.entry x (fst b) ∈ˢ graphB ⟩ → EntryIndex x b
graphB-entry-out x b he = PT.rec PT.squash₁
  (λ { (z , rest) → PT.rec PT.squash₁
    (λ { (p , rest') → PT.rec PT.squash₁
      (λ { (hp , source , path) → translated z p hp source path }) rest' }) rest })
  (subst ⟨_⟩ (BG.Translation.trᴮ-entries Graph.graphCode _) he)
  where
  translated : (z p : S) (hp : ⟨ p ∈ˢ BG.NG.C.carrier ⟩)
    → ⟨ BG.BK.entry z p ∈ˢ Graph.graphCode ⟩
    → ⟨ BG.BK.entry x (fst b) ≈ˢ BG.BK.entry (BG.Translation.trᴮ z) (fst (i (p , hp))) ⟩
    → EntryIndex x b
  translated z p hp source path = PT.rec PT.squash₁
    (λ { (α , hα , rest) → PT.rec PT.squash₁
      (λ { (q , hq , sourcepath) → ∣ α , hα , (p , hp) ,
        fst (BG.BK.entry-inj (≈→≡ path)) ∙
          cong BG.Translation.trᴮ (fst (BG.NG.K.entry-inj (≈→≡ sourcepath))) ,
        Pt≡ (snd (BG.BK.entry-inj (≈→≡ path))) ∣₁ }) rest })
    (subst ⟨_⟩ (Indexed.indexed-spec κ (λ a → fst (Graph.vertex a)) _)
      (subst (λ e → ⟨ e ∈ˢ Graph.graphCode ⟩) (BG.entry-agrees z p) source))

graphB-entry-spec : (x : S) (b : Pt BG.B)
  → (BG.BK.entry x (fst b) ∈ˢ graphB) ≡ (EntryIndex x b , PT.squash₁)
graphB-entry-spec x b = ⇔toPath (graphB-entry-out x b)
  (PT.rec (snd (BG.BK.entry x (fst b) ∈ˢ graphB))
    (λ { (α , hα , p , xpath , bpath) →
      subst (λ y → ⟨ BG.BK.entry y (fst b) ∈ˢ graphB ⟩) (sym xpath)
        (subst (λ c → ⟨ BG.BK.entry (vertexB α) (fst c) ∈ˢ graphB ⟩)
          (sym bpath) (graphB-entry α hα p)) }))

graphB-support-out : (x : S) → ⟨ x ∈ˢ BG.BSupport.support graphB ⟩
  → ∥ Σ[ α ∈ S ] (⟨ α ∈ˢ κ ⟩ × (x ≡ vertexB α)) ∥₁
graphB-support-out x hx = PT.rec PT.squash₁
  (λ { (b , hb , he) → PT.map (λ { (α , hα , p , xpath , bpath) → α , hα , xpath })
    (graphB-entry-out x (b , hb) he) })
  (BG.BSupport.entry-out graphB x hx)

graphB-support-in : (α : S) → ⟨ α ∈ˢ κ ⟩
  → ⟨ vertexB α ∈ˢ BG.BSupport.support graphB ⟩
graphB-support-in α hα = PT.rec (snd (vertexB α ∈ˢ BG.BSupport.support graphB))
  (λ p → BG.BSupport.entry-in graphB (vertexB α) (fst (i p)) (snd (i p))
    (graphB-entry α hα p)) inhabited
  where
  inhabited : ∥ Cond ∥₁
  inhabited = K5.Frame.Poset.ForcingBase.inhabited (BG.Base.codedBase lem)

graphB-support-spec : (x : S) → (x ∈ˢ BG.BSupport.support graphB)
  ≡ (∥ Σ[ α ∈ S ] (⟨ α ∈ˢ κ ⟩ × (x ≡ vertexB α)) ∥₁ , PT.squash₁)
graphB-support-spec x = ⇔toPath (graphB-support-out x)
  (PT.rec (snd (x ∈ˢ BG.BSupport.support graphB))
    (λ { (α , hα , xpath) → subst (λ y → ⟨ y ∈ˢ BG.BSupport.support graphB ⟩)
      (sym xpath) (graphB-support-in α hα) }))

graphB-weight : (α : S) → ⟨ α ∈ˢ κ ⟩ → BG.weight graphB (vertexB α) ≡ ⊤ᴮ
graphB-weight α hα = Separation.all-force-top lem (BG.weight graphB (vertexB α))
  (λ p → FF.⊩ᴮ-intro p _ (BG.weight-upper graphB (vertexB α) (i p) (graphB-entry α hα p)))

graphB-member-upper : (z α : S) → ⟨ α ∈ˢ κ ⟩
  → ⟨ eq z (vertexB α) ≤ᴮ mem z graphB ⟩
graphB-member-upper z α hα = subst (λ v → ⟨ v ≤ᴮ mem z graphB ⟩)
  (cong (λ b → b ⊓ᴮ eq z (vertexB α)) (graphB-weight α hα)
    ∙ ⊓-comm ⊤ᴮ (eq z (vertexB α)) ∙ ⊓-⊤ (eq z (vertexB α)))
  (BG.Atomic.∈ᴮ-ub z graphB (vertexB α) (graphB-support-in α hα))

graphB-member-least : (z : S) (v : Pt BG.B)
  → ((α : S) → ⟨ α ∈ˢ κ ⟩ → ⟨ eq z (vertexB α) ≤ᴮ v ⟩)
  → ⟨ mem z graphB ≤ᴮ v ⟩
graphB-member-least z v upper = BG.Atomic.∈ᴮ-lub z graphB v
  (λ x hx → PT.rec (snd ((BG.weight graphB x ⊓ᴮ eq z x) ≤ᴮ v))
    (λ { (α , hα , xpath) → ⊆ˢ-trans (⊓-lb₂ (BG.weight graphB x) (eq z x))
      (subst (λ y → ⟨ eq z y ≤ᴮ v ⟩) (sym xpath) (upper α hα)) })
    (graphB-support-out x hx))

graphB-member-characterization : (z : S) (v : Pt BG.B)
  → (mem z graphB ≤ᴮ v)
    ≡ ⋀ S (λ α → (α ∈ˢ κ) ⇒ (eq z (vertexB α) ≤ᴮ v))
graphB-member-characterization z v = ⇔toPath
  (λ bound α hα → ⊆ˢ-trans (graphB-member-upper z α hα) bound)
  (graphB-member-least z v)

graphB-vertex-member : (α : S) → ⟨ α ∈ˢ κ ⟩ → mem (vertexB α) graphB ≡ ⊤ᴮ
graphB-vertex-member α hα = ≤ᴮ-antisym (⊤-greatest (mem (vertexB α) graphB))
  (subst (λ b → ⟨ b ≤ᴮ mem (vertexB α) graphB ⟩) (BG.Laws.≈ᴮ-refl (vertexB α))
    (graphB-member-upper (vertexB α) α hα))

indexed-functional : (α β : S)
  → ⟨ eq (BG.translated-check α) (BG.translated-check β) ≤ᴮ eq (Reals.realB α) (Reals.realB β) ⟩
indexed-functional α β = decide (lem (α ≈ˢ β))
  where
  decide : ⟨ α ≈ˢ β ⟩ ⊎ (⟨ α ≈ˢ β ⟩ → Empty.⊥)
    → ⟨ eq (BG.translated-check α) (BG.translated-check β) ≤ᴮ eq (Reals.realB α) (Reals.realB β) ⟩
  decide (inl same) = subst
    (λ b → ⟨ eq (BG.translated-check α) (BG.translated-check β) ≤ᴮ b ⟩)
    (sym (cong (λ a → eq (Reals.realB α) (Reals.realB a)) (sym (≈→≡ same))
      ∙ BG.Laws.≈ᴮ-refl (Reals.realB α)))
    (⊤-greatest (eq (BG.translated-check α) (BG.translated-check β)))
  decide (inr different) = subst
    (λ b → ⟨ b ≤ᴮ eq (Reals.realB α) (Reals.realB β) ⟩)
    (sym (BG.translated-check-distinct α β (λ h → Empty.rec (different h))))
    (⊥-least (eq (Reals.realB α) (Reals.realB β)))

module Distinct
  (find : OrdinaryProfile.FoundationInduction 𝒮)
  (hw : ⟨ CardinalBridge.isOmega 𝒮 w ⟩)
  where

  module D = Reals.DenseDistinct find hw using ( distinct-top )

  indexed-injective : (α β : S) → ⟨ α ∈ˢ κ ⟩ → ⟨ β ∈ˢ κ ⟩
    → ⟨ eq (Reals.realB α) (Reals.realB β) ≤ᴮ eq (BG.translated-check α) (BG.translated-check β) ⟩
  indexed-injective α β hα hβ = decide (lem (α ≈ˢ β))
    where
    decide : ⟨ α ≈ˢ β ⟩ ⊎ (⟨ α ≈ˢ β ⟩ → Empty.⊥)
      → ⟨ eq (Reals.realB α) (Reals.realB β) ≤ᴮ eq (BG.translated-check α) (BG.translated-check β) ⟩
    decide (inl same) = subst
      (λ b → ⟨ eq (Reals.realB α) (Reals.realB β) ≤ᴮ b ⟩)
      (sym (cong (λ a → eq (BG.translated-check α) (BG.translated-check a)) (sym (≈→≡ same))
        ∙ BG.Laws.≈ᴮ-refl (BG.translated-check α)))
      (⊤-greatest (eq (Reals.realB α) (Reals.realB β)))
    decide (inr different) = subst
      (λ b → ⟨ b ≤ᴮ eq (BG.translated-check α) (BG.translated-check β) ⟩)
      (sym zero-value) (⊥-least (eq (BG.translated-check α) (BG.translated-check β)))
      where
      value : Pt BG.B
      value = eq (Reals.realB α) (Reals.realB β)

      zero-value : value ≡ ⊥ᴮ
      zero-value = ≤-both-⊥ value value (≤ᴮ-refl value)
        (subst (λ b → ⟨ value ≤ᴮ b ⟩)
          (sym (D.distinct-top α β hα hβ (λ h → Empty.rec (different h)))) (⊤-greatest value))

  indexed-equality : (α β : S) → ⟨ α ∈ˢ κ ⟩ → ⟨ β ∈ˢ κ ⟩
    → eq (Reals.realB α) (Reals.realB β) ≡ eq (BG.translated-check α) (BG.translated-check β)
  indexed-equality α β hα hβ = ≤ᴮ-antisym
    (indexed-injective α β hα hβ) (indexed-functional α β)

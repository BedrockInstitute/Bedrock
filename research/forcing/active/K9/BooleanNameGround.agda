{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile

module K9.BooleanNameGround
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (families : NameKernel.Families 𝒮)
  (accessible : NameKernel.Accessibility 𝒮)
  (images : NameKernel.MemberImage 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (κ w : ZFStructure.S 𝒮)
  (lem : LEM ℓ)
  where

open import FOL.ZFStructure using ( module hPropStructure )
import Cubical.Induction.WellFounded as WFI
import Cubical.HITs.PropositionalTruncation as PT
import Cubical.Data.Empty as Empty
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Functions.Logic using ( ⇔toPath )
import CodedVocabulary
import GroundDescription
import NameSupport
import StandardNames
import TranslateForward
import K4.Algebra
import K4.Atomic
import K4.AtomicLaws
import K4.CheckValues
import K4.ValueSets
import K4.InstanceCoded
import CodedCompletion
import K5.InstanceBase
import K5.Frame
import K9.NameGround
import K9.TranslatedCheck

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open PT using ( ∥_∥₁; ∣_∣₁ )
import K9.BooleanSupport
module SupportGround = K9.BooleanSupport 𝒮 families accessible images pow κ w lem
  using ( B; weight; weight-upper; weight-least; entry-agrees
  ; source-entry-in; source-entry-out; source-weight-in; source-weight-out; source-child-name; source-check-spec
  ; module NG; module Base; module IC; module BK; module PSupport; module BSupport; module Checked )
open SupportGround public using ( B; weight; weight-upper; weight-least; entry-agrees
  ; source-entry-in; source-entry-out; source-weight-in; source-weight-out; source-child-name; source-check-spec
  ; module NG; module Base; module IC; module BK; module PSupport; module BSupport; module Checked )
open NG using ( extensional; ≈ˢ-paths; hasUnion; hasSeparation )
open K4.Algebra 𝒮 using ( Pt; _≤ᴮ_ )
open K4.Algebra.Lattice IC.codedLattice using ( ⊤ᴮ; ⊥ᴮ )
private module GD = GroundDescription 𝒮 extensional ≈ˢ-paths using ( ext-path )

import K9.BooleanAtomic
import K9.BooleanTranslation
module Atomic = K9.BooleanAtomic.Atomic 𝒮 families accessible images pow κ w lem
  using ( _≈ᴮ_; _∈ᴮ_; ∈ᴮ-ub; ∈ᴮ-lub; ≈ᴮ-lbˡ; ≈ᴮ-lbʳ; ≈ᴮ-glb; ≈ᴮ-sym )
module Laws = K9.BooleanAtomic.Laws 𝒮 families accessible images pow κ w lem
  using ( ≈ᴮ-refl; ≈ᴮ-trans; ext-≈ᴮ; ∈ᴮ-empty; ∈ᴮ-congʳ; ∈ᴮ-congˡ )
module Translation = K9.BooleanTranslation.Translation 𝒮 families accessible images pow κ w lem
  using ( trᴮ; trᴮ-entries; trᴮ-name )


translated-check : S → S
translated-check a = Translation.trᴮ (NG.Check.chk a)

module CheckNames = K9.TranslatedCheck.Names 𝒮 extensional ≈ˢ-paths
  NG.C.carrier NG.C.order B IC.codedLattice IC.codedComplement IC.codedComplete (Base.codedBase lem)
  (λ P step → WFI.WFI.induction accessible step)
  BK.entry BK.entry-inj NG.Check.chk Checked.check Translation.trᴮ source-check-spec Checked.check-spec
  Translation.trᴮ-entries BSupport.support BSupport.entry-in BSupport.entry-out weight weight-upper
  using ( translated; module Values )

module Compare = CheckNames.Values Atomic._≈ᴮ_ Atomic._∈ᴮ_
  Atomic.∈ᴮ-ub Atomic.≈ᴮ-glb Atomic.≈ᴮ-sym Laws.≈ᴮ-trans
  using ( comparison; equality-values )

translated-check-comparison : (a : S) → Atomic._≈ᴮ_ (translated-check a) (Checked.check a) ≡ ⊤ᴮ
translated-check-comparison = Compare.comparison lem

translated-check-equality : (a b : S)
  → Atomic._≈ᴮ_ (translated-check a) (translated-check b) ≡ Atomic._≈ᴮ_ (Checked.check a) (Checked.check b)
translated-check-equality = Compare.equality-values lem

import K9.BooleanCheckReflection
module Reflection = K9.BooleanCheckReflection.Reflection 𝒮 families accessible images pow κ w lem
  using ( check-reflects-≈ )

translated-check-distinct : (a b : S) → (⟨ a ≈ˢ b ⟩ → ⟨ ⊥ ⟩)
  → Atomic._≈ᴮ_ (translated-check a) (translated-check b) ≡ ⊥ᴮ
translated-check-distinct a b different = decide (Reflection.check-reflects-≈ a b)
  where
  decide : ((Atomic._≈ᴮ_ (Checked.check a) (Checked.check b) ≡ ⊤ᴮ) × ⟨ a ≈ˢ b ⟩)
    ⊎ ((Atomic._≈ᴮ_ (Checked.check a) (Checked.check b) ≡ ⊥ᴮ) × (⟨ a ≈ˢ b ⟩ → Empty.⊥))
    → Atomic._≈ᴮ_ (translated-check a) (translated-check b) ≡ ⊥ᴮ
  decide (inl (top , same)) = Empty.rec* (different same)
  decide (inr (bottom , different')) = translated-check-equality a b ∙ bottom

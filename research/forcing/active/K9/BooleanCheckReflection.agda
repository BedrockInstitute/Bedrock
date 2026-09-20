{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile

module K9.BooleanCheckReflection
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
open import Cubical.Data.Sum using ( inl; inr )
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
open SupportGround public using ( B; weight; weight-upper; weight-least; entry-agrees
  ; source-entry-in; source-entry-out; source-weight-in; source-weight-out; source-child-name; source-check-spec
  ; module NG; module Base; module IC; module BK; module PSupport; module BSupport; module Checked )
open NG using ( extensional; ≈ˢ-paths; hasUnion; hasSeparation )
open K4.Algebra 𝒮 using ( Pt; _≤ᴮ_ )
open K4.Algebra.Lattice IC.codedLattice using ( ⊤ᴮ; ⊥ᴮ )
private module GD = GroundDescription 𝒮 extensional ≈ˢ-paths using ( ext-path )

import K9.BooleanAtomic
import K9.BooleanTranslation
module Atoms = K9.BooleanAtomic 𝒮 families accessible images pow κ w lem using ( module Atomic; module Laws )
open Atoms public using ( module Atomic; module Laws )
module Translate = K9.BooleanTranslation 𝒮 families accessible images pow κ w lem using ( module Translation )
open Translate public using ( module Translation )

nontrivial : ⊤ᴮ ≡ ⊥ᴮ → Empty.⊥
nontrivial e = PT.rec Empty.isProp⊥
  (λ p → Empty.rec* (IC.codedNontrivial p (sym e)))
  (K5.Frame.Poset.ForcingBase.inhabited (Base.codedBase lem))

module Reflection = K4.CheckValues.Core.Names.Values.Classical 𝒮 extensional ≈ˢ-paths
  B IC.codedLattice IC.codedComplement IC.codedComplete
  BK.Child BK.RawRec.result BSupport.support BSupport.support-out weight
  BK.entry BK.entry-inj (λ x b n h → ∣ b , h ∣₁) (λ x n h → h)
  BK.IsName BSupport.support-in weight-upper weight-least
  Checked.check Checked.check-spec Checked.check-name
  Atomic._≈ᴮ_ Atomic._∈ᴮ_ Atomic.∈ᴮ-ub Atomic.∈ᴮ-lub
  Atomic.≈ᴮ-lbˡ Atomic.≈ᴮ-lbʳ Atomic.≈ᴮ-sym
  Laws.≈ᴮ-refl Laws.≈ᴮ-trans Laws.ext-≈ᴮ Laws.∈ᴮ-empty
  lem nontrivial
  using ( check-reflects-≈ ; module Delta0 )

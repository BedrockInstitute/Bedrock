{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile

module K9.BooleanTranslation
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

closed : S → Ω
closed D = ⋀ S (λ n → (n ∈ˢ D) ⇒ ⋀ S (λ e → (e ∈ˢ n) ⇒
  ⋁ S (λ y → ⋁ S (λ b → (y ∈ˢ D) ⊓ ((b ∈ˢ B) ⊓ (e ≈ˢ BK.entry y b))))))

closed-intro : (D : S)
  → ((n : S) → ⟨ n ∈ˢ D ⟩ → (e : S) → ⟨ e ∈ˢ n ⟩
    → ∥ Σ[ y ∈ S ] Σ[ b ∈ S ] (⟨ y ∈ˢ D ⟩ × ⟨ b ∈ˢ B ⟩ × (e ≡ BK.entry y b)) ∥₁)
  → ⟨ closed D ⟩
closed-intro D h n hn e he = PT.rec PT.squash₁
  (λ { (y , b , hy , hb , path) → ∣ y , ∣ b , hy , hb ,
    subst ⟨_⟩ (sym (≈ˢ-paths e (BK.entry y b))) path ∣₁ ∣₁ }) (h n hn e he)

module Translation = TranslateForward.Kernel.Weighted.Source.Target 𝒮
  BK.entry BK.entry-inj BK.Child BK.isPropChild (λ x b n h → ∣ b , h ∣₁) (λ x n h → h)
  BK.child-wf ≈ˢ-paths GD.ext-path
  (NameKernel.MemberImage.image images) (NameKernel.MemberImage.image-spec images)
  NG.Union.bigUnion NG.Union.bigUnion-spec
  NG.C.carrier NG.K.IsName source-child-name
  PSupport.support source-entry-in source-entry-out
  PSupport.weightsAt PSupport.weightsAt-sub source-weight-in source-weight-out
  B BK.IsName BK.name-intro BSupport.support BSupport.entry-in BSupport.entry-out
  closed closed-intro (λ p → fst (Base.iᴷ p)) (λ p → snd (Base.iᴷ p))
  using ( trᴮ; trᴮ-entries; trᴮ-name )

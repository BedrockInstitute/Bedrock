{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.159] Probe B.  THE PROFILE, CONFIRMED WITH A WALL CLOCK.
--
-- Probe A (= [LJ-1.156] Probe D) WITH `κ-min-at` AND ITS `where` BLOCK
-- DELETED.  Nothing else changes.
--
-- WHY.  `agda --profile=definitions` on Probe A puts 82,763 ms of 99,310
-- in `κ-min-at` and its six `where` bindings, which is 83.3 percent of
-- the file over 13 source lines.  A profile is not a wall clock, so this
-- file measures the same claim with the clock: it should cost about 17 s.
--
-- ABORT CRITERION: none.  These probes are a bisection, not a decision.
-- The decision criterion is in agents/tasks/LJ-1-159/lj-1.159-report.md
-- section 0 and it was fixed before any run.
--
-- Tracked probe; ONE agda process under GHCRTS="-A64m -I0 -M8g";
-- never committed to src/.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-159.ProbeLJ1159B {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

import L.Ordinal.SquareLaw {ℓ} lem as SQ
open SQ using ( module FiniteBase; ordSWO )
import L.Ordinal {ℓ} as Ord
open Ord using ( mem-ord; suc-ord; ω-ord; #∈ω )
open import L.Constructible {ℓ} using ( IsOrd )
import L.Ordinal.Linear {ℓ} lem as Lin
open Lin using ( ord-tri )
import FOL.Count {ℓ} as Count
import L.Choice.Finite {ℓ} lem as LF
open LF using ( natOrder )
import V.Hierarchy {ℓ} as Hier
open Hier using ( 𝒮ᵥ; ∈-irrefl; ∈-induction )
import V.Model {ℓ} as VModel
open VModel using ( ∈sucV-elim; ∈sucV-inl; self∈sucV )
import V.Presentation {ℓ} as VPres
open VPres using ( member; fiber; ↪-inj )
import V.Coding {ℓ} as VCoding
open VCoding using ( #-inj′ )
import FOL.ZFStructure as ZF
open ZF using ( module hPropStructure )
import Cubical.HITs.CumulativeHierarchy.Base as CHB
open CHB using ( setIsSet )
import Cubical.HITs.CumulativeHierarchy.Properties as CH
open CH using ( ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; isEmb⟪_⟫↪; ∈ₛ⟪_⟫↪_ )
import Cubical.HITs.CumulativeHierarchy.Constructions as CHC
open CHC using ( module InfinitySet )
open InfinitySet {ℓ} using ( ω; sucV; #_ )
import Cubical.Functions.Embedding as Emb
open Emb using ( isEmbedding→hasPropFibers; Embedding-into-isSet→isSet )
import Cubical.Data.Sigma as Sig
open Sig using ( ΣPathP; Σ≡Prop )
import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ} as WOBase
open WOBase using ( SWO; IsLeast; leastOf; module SWO )
import Cubical.Data.Nat as Nat
open Nat using ( ℕ; zero; suc )
import Cubical.Data.Nat.Properties as NatProp
open NatProp using ( injSuc; znots; snotz )
import Cubical.Data.Sum as Sum
open Sum using ( _⊎_; inl; inr )
import Cubical.Data.Sum.Properties as SumProp
open SumProp using ( isProp⊎ )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

open hPropStructure 𝒮ᵥ

-- The injection type.  [LJ-1.107] took this from ProbeLJ194A; it is three

_↪_ : Type ℓ → Type ℓ → Type ℓ
X ↪ Y = Σ[ f ∈ (X → Y) ] ((x y : X) → f x ≡ f y → x ≡ y)

isSet⟪_⟫ : (a : S) → isSet ⟪ a ⟫
isSet⟪ a ⟫ = Embedding-into-isSet→isSet (⟪ a ⟫↪ , isEmb⟪ a ⟫↪) setIsSet


module LeastCardInj (α : S) (oα : IsOrd α) where

  Inj : S → Type ℓ
  Inj γ = ⟪ α ⟫ ↪ ⟪ γ ⟫

  InjP : S → hProp ℓ
  InjP γ = ∥ Inj γ ∥₁ , squash₁

  InjP' : ⟪ sucV α ⟫ → hProp ℓ
  InjP' γ = InjP (⟪ sucV α ⟫↪ γ)

  w : SWO (⟪ sucV α ⟫)
  w = ordSWO (sucV α) (suc-ord oα)

  self : ⟪ sucV α ⟫
  self = fiber (sucV α) (self∈sucV α) .fst

  self-eq : ⟪ sucV α ⟫↪ self ≡ α
  self-eq = fiber (sucV α) (self∈sucV α) .snd

  idInj : ⟪ α ⟫ ↪ ⟪ α ⟫
  idInj = (λ x → x) , (λ x y e → e)

  nonempty : ∥ Σ[ b ∈ ⟪ sucV α ⟫ ] ⟨ InjP' b ⟩ ∥₁
  nonempty = ∣ self , subst (λ v → ∥ ⟪ α ⟫ ↪ ⟪ v ⟫ ∥₁) (sym self-eq) ∣ idInj ∣₁ ∣₁

  least : Σ[ γ ∈ ⟪ sucV α ⟫ ] IsLeast w InjP' γ
  least = leastOf w lem InjP' nonempty

  γ-card : ⟪ sucV α ⟫
  γ-card = fst least

  κ : S
  κ = ⟪ sucV α ⟫↪ γ-card

  oκ : IsOrd κ
  oκ = mem-ord {A = sucV α} (suc-ord oα) κ (member (sucV α) γ-card)

  κ∈sα : ⟨ κ ∈ˢ sucV α ⟩
  κ∈sα = member (sucV α) γ-card

  κ-inj : ∥ ⟪ α ⟫ ↪ ⟪ κ ⟫ ∥₁
  κ-inj = fst (snd least)

  κ-min : (b : ⟪ sucV α ⟫) → ⟨ InjP' b ⟩ → (SWO._<∙_ w b γ-card → Empty.⊥)
  κ-min = snd (snd least)

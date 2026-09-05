{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.159] Probe C.  THE CURE.  THE AMBIENT ORDINAL IS A PARAMETER.
--
-- THE CURE UNDER TEST.  `sucV α` NEVER APPEARS IN A TYPE.
--
-- Probe A states every type over `⟪ sucV α ⟫`.  `sucV N = N ∪ ⁅ N ⁆s`
-- and `a ∪ b = ⋃ ⁅ a , b ⁆`, so `sucV α` reduces to a three-layer `sett`
-- even when `α` is a variable, and `⟪ _ ⟫ = V-repr _ .fst .fst` then
-- walks the monic-presentation construction at every conversion.  That
-- is `dev/LESSONS.md` P-l, at the site P-l names.
--
-- THE CHANGE.  The ambient ordinal is a PARAMETER `sα`, with `α ∈ˢ sα`
-- supplied.  Nothing else moves: the same `ordSWO`, the same `leastOf`,
-- the same predicate, the same six `where` bindings, line for line.
-- `IsOrd α` is not needed at all once `sα` is a parameter.
--
-- IT IS ALSO THE DD4 ANSWER.  `sα` is any ordinal that has `α` as a
-- member, so the module is generic in the ambient ordinal rather than
-- fixed to the successor.
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

module LJ-1-159.ProbeLJ1159C {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

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


module LeastCardAt (sα : S) (osα : IsOrd sα) (α : S) (α∈sα : ⟨ α ∈ˢ sα ⟩) where

  Inj : S → Type ℓ
  Inj γ = ⟪ α ⟫ ↪ ⟪ γ ⟫

  InjP : S → hProp ℓ
  InjP γ = ∥ Inj γ ∥₁ , squash₁

  InjP' : ⟪ sα ⟫ → hProp ℓ
  InjP' γ = InjP (⟪ sα ⟫↪ γ)

  w : SWO (⟪ sα ⟫)
  w = ordSWO sα osα

  self : ⟪ sα ⟫
  self = fiber sα α∈sα .fst

  self-eq : ⟪ sα ⟫↪ self ≡ α
  self-eq = fiber sα α∈sα .snd

  idInj : ⟪ α ⟫ ↪ ⟪ α ⟫
  idInj = (λ x → x) , (λ x y e → e)

  nonempty : ∥ Σ[ b ∈ ⟪ sα ⟫ ] ⟨ InjP' b ⟩ ∥₁
  nonempty = ∣ self , subst (λ v → ∥ ⟪ α ⟫ ↪ ⟪ v ⟫ ∥₁) (sym self-eq) ∣ idInj ∣₁ ∣₁

  least : Σ[ γ ∈ ⟪ sα ⟫ ] IsLeast w InjP' γ
  least = leastOf w lem InjP' nonempty

  γ-card : ⟪ sα ⟫
  γ-card = fst least

  κ : S
  κ = ⟪ sα ⟫↪ γ-card

  oκ : IsOrd κ
  oκ = mem-ord {A = sα} osα κ (member sα γ-card)

  κ∈sα : ⟨ κ ∈ˢ sα ⟩
  κ∈sα = member sα γ-card

  κ-inj : ∥ ⟪ α ⟫ ↪ ⟪ κ ⟫ ∥₁
  κ-inj = fst (snd least)

  κ-min : (b : ⟪ sα ⟫) → ⟨ InjP' b ⟩ → (SWO._<∙_ w b γ-card → Empty.⊥)
  κ-min = snd (snd least)

  κ-min-at : (δ : S) → ⟨ δ ∈ˢ κ ⟩ → ∥ ⟪ α ⟫ ↪ ⟪ δ ⟫ ∥₁ → Empty.⊥
  κ-min-at δ δ∈κ α↪δ = κ-min b bInjP b<γ
    where
    δ∈sα : ⟨ δ ∈ˢ sα ⟩
    δ∈sα = osα .fst {x = κ} {y = δ} δ∈κ (member sα γ-card)
    b : ⟪ sα ⟫
    b = fiber sα δ∈sα .fst
    bδ : ⟪ sα ⟫↪ b ≡ δ
    bδ = fiber sα δ∈sα .snd
    bInjP : ⟨ InjP' b ⟩
    bInjP = subst (λ v → ∥ ⟪ α ⟫ ↪ ⟪ v ⟫ ∥₁) (sym bδ) α↪δ
    b<γ : SWO._<∙_ w b γ-card
    b<γ = subst (λ z → ⟨ z ∈ˢ κ ⟩) (sym bδ) δ∈κ

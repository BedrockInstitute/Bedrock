{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.156] Probe E.  THE A/B ON THE ONE DESIGN CHANGE.
--
-- LEASTNESS OVER BIJECTIONS, alone.  [LJ-1.107]'s `LeastCard`
-- (agents/tasks/LJ-1-107/ProbeLJ1107A.agda:217-266) verbatim.
--
-- Probe D and Probe E carry the SAME import block as Probe A and the
-- SAME `leastOf` over `⟪ sucV α ⟫`.  The ONLY difference between them is
-- the predicate: an INJECTION in D, an EQUIVALENCE in E.  [LJ-1.107]
-- measured its `LeastCard` step at 91.98 s and called it the dominant
-- term (agents/tasks/LJ-1-107/lj-1.107-report.md:52).  This pair asks
-- whether the swap moves that term.
--
-- ABORT CRITERION: none.  This pair is a measurement, not a decision.
--
-- Tracked probe; ONE agda process under GHCRTS="-A64m -I0 -M8g";
-- never committed to src/.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-156.ProbeLJ1156E {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

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
open import Cubical.Foundations.Equiv using ( _≃_; idEquiv )

-- [LJ-1.107]'s LeastCard, verbatim, at agents/tasks/LJ-1-107/ProbeLJ1107A.agda:217-266.
module LeastCard (α : S) (oα : IsOrd α) where

  Eq : S → Type ℓ
  Eq γ = ⟪ γ ⟫ ≃ ⟪ α ⟫

  EqP : S → hProp ℓ
  EqP γ = ∥ Eq γ ∥₁ , squash₁

  EqP' : ⟪ sucV α ⟫ → hProp ℓ
  EqP' γ = EqP (⟪ sucV α ⟫↪ γ)

  w : SWO (⟪ sucV α ⟫)
  w = ordSWO (sucV α) (suc-ord oα)

  least : Σ[ γ ∈ ⟪ sucV α ⟫ ] IsLeast w EqP' γ
  least = leastOf w lem EqP'
    (∣ fiber (sucV α) (self∈sucV α) .fst , ∣ idEquiv (⟪ α ⟫) ∣₁ ∣₁)

  γ-card : ⟪ sucV α ⟫
  γ-card = fst least

  κ : S
  κ = ⟪ sucV α ⟫↪ γ-card

  oκ : IsOrd κ
  oκ = mem-ord {A = sucV α} (suc-ord oα) κ (member (sucV α) γ-card)

  κ∈sα : ⟨ κ ∈ˢ sucV α ⟩
  κ∈sα = member (sucV α) γ-card

  κ-eqα : ∥ ⟪ κ ⟫ ≃ ⟪ α ⟫ ∥₁
  κ-eqα = fst (snd least)

  κ-min : (b : ⟪ sucV α ⟫) → ⟨ EqP' b ⟩ → (SWO._<∙_ w b γ-card → Empty.⊥)
  κ-min = snd (snd least)

  -- the leastness at a member δ of κ: δ < κ with δ ≃ α is absurd
  κ-min-at : (δ : S) → ⟨ δ ∈ˢ κ ⟩ → ∥ ⟪ δ ⟫ ≃ ⟪ α ⟫ ∥₁ → Empty.⊥
  κ-min-at δ δ∈κ δ≃α = κ-min b (bEqP) b<γ
    where
    δ∈sα : ⟨ δ ∈ˢ sucV α ⟩
    δ∈sα = suc-ord oα .fst {x = κ} {y = δ} δ∈κ (member (sucV α) γ-card)
    b : ⟪ sucV α ⟫
    b = fiber (sucV α) δ∈sα .fst
    bδ : ⟪ sucV α ⟫↪ b ≡ δ
    bδ = fiber (sucV α) δ∈sα .snd
    bEqP : ⟨ EqP' b ⟩
    bEqP = subst (λ v → ∥ ⟪ v ⟫ ≃ ⟪ α ⟫ ∥₁) (sym bδ) δ≃α
    b<γ : SWO._<∙_ w b γ-card
    b<γ = subst (λ z → ⟨ z ∈ˢ κ ⟩) (sym bδ) δ∈κ

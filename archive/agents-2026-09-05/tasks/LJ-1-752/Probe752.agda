{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.752] PROBE.  A member of a finite iterate's stage sits in Lset of
-- the ordinal, under closedω:
--
--   block∈Lγ :
--       (γ : V ℓ) (oγ : IsOrd γ) (clγ : closedω γ)
--       (x : V ℓ) → ⟨ x ∈ˢ γ ⟩ →
--       (n : ℕ) (b : V ℓ) →
--       ⟨ b ∈ˢ Lset (sucIter n x) ⟩ → ⟨ b ∈ˢ Lset γ ⟩
--
-- Route:  `sucIter-in-γ` (delivered GO at
-- agents/tasks/LJ-1-751/Probe751.agda:91) puts the iterate inside γ, and
-- ONE `Lset-mono` application (src/L/Constructible.lagda.md:365) lifts the
-- stage membership along that inclusion.
--
-- `sucIter-in-γ` and its closer are transcribed here, token for token from
-- agents/tasks/LJ-1-751/Probe751.agda:58-99, and NOT imported.  The reason
-- is hermeticity, one step past the trade 751 recorded:  nothing typechecks
-- a probe once its task closes (agents/README.md), and `archive/` is not an
-- include root of bedrock.agda-lib (it lists `src agents/tasks` only), so a
-- cross-probe import dies the day the other probe retires under `archive/`,
-- which the post-LJ-1 collection pass is queued to do.  The chain
-- 737-SPLIT -> 747 -> 751 is the same transcription trade, each recorded at
-- its own site.
--
-- THE BRIEF'S OBLIGATION BLOCK DROPPED ONE ARROW (after `⟨ x ∈ˢ γ ⟩`), the
-- same slip [LJ-1.751] measured and fixed
-- (agents/tasks/LJ-1-751/lj-1.751-report.md, section "THE BRIEF'S
-- OBLIGATION BLOCK DROPPED ONE ARROW").  This file inserts that one arrow
-- and nothing else; the delivered statement is the brief's named
-- statement, no weakening.
--
-- Lands nothing in src/.  `table-sat` is NOT inhabited; this file imports
-- and names no satisfaction machinery of the tree.
--
-- ONE Agda process per run, GHCRTS wide caliber, set on the pane by the
-- program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-752.Probe752 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import V.Model {ℓ} using ( ∈sucV-elim )
open import L.Constructible {ℓ} using ( IsOrd; Lset; Lset-mono )
open import L.Ordinal {ℓ} using ( mem-ord )
open import L.Ordinal.Stages {ℓ} lem using ( suc∈or≡ )
open import L.Ordinal.StageArith {ℓ} lem
  using ( sucIter; +ω; +ω-mem; closedω )

open import Cubical.Data.Sum as Sum using ( _⊎_ )
import Cubical.Data.Empty as Empty
open import Cubical.Foundations.HLevels using ( isOfHLevelLift )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

------------------------------------------------------------------------------
-- SECTION 0.  The 751 delivered term, token for token from
-- agents/tasks/LJ-1-751/Probe751.agda:58-99.  Its closer is itself the 747
-- closer (agents/tasks/LJ-1-747/Probe747.agda:65-87) with the
-- `hγ : ⟨ isL γ ⟩` argument trimmed, which is the 737-SPLIT closer one trim
-- up the chain.  The only import this file adds over the 751 file is
-- `Lset` and `Lset-mono` from src/L/Constructible.lagda.md.

module Closer (γ : V ℓ) (oγ : IsOrd γ) (clγ : closedω γ) where

  -- closedω forbids γ to be a successor:  γ = sucV x with x ∈ γ would
  -- put +ω x inside sucV x, and +ω x is neither below nor equal to x.
  no-succ : (x : V ℓ) → ⟨ x ∈ˢ γ ⟩ → sucV x ≡ γ → Empty.⊥
  no-succ x x∈ eq = lower
    (∈sucV-elim (isOfHLevelLift 1 Empty.isProp⊥) +ω∈sucx
      (λ h → lift (kA h)) (λ h → lift (k≡ h)))
    where
    ox : IsOrd x
    ox = mem-ord {A = γ} oγ x x∈
    +ω∈sucx : ⟨ +ω x ∈ˢ sucV x ⟩
    +ω∈sucx = subst (λ w → ⟨ +ω x ∈ˢ w ⟩) (sym eq) (clγ x x∈)
    kA : ⟨ +ω x ∈ˢ x ⟩ → Empty.⊥
    kA h = ∈-irrefl x (ox .fst (+ω-mem x) h)
    k≡ : +ω x ≡ x → Empty.⊥
    k≡ h≡ = ∈-irrefl x (subst (λ w → ⟨ x ∈ˢ w ⟩) h≡ (+ω-mem x))

  -- The strict successor step:  closedω makes every successor of a
  -- member a member.
  suc∈γ : (x : V ℓ) → ⟨ x ∈ˢ γ ⟩ → ⟨ sucV x ∈ˢ γ ⟩
  suc∈γ x x∈ = Sum.rec id (λ h → Empty.rec (no-succ x x∈ h))
    (suc∈or≡ x γ (mem-ord {A = γ} oγ x x∈) oγ x∈)

-- Induction on `n`:  the zero clause is the identity law of `sucIter`
-- (src/L/Ordinal/StageArith.lagda.md:35), so the hypothesis passes
-- through; the successor clause computes `sucIter (suc n) x` to
-- `sucV (sucIter n x)` (src/L/Ordinal/StageArith.lagda.md:36) and applies
-- the 747 step at the previous iterate.
sucIter-in-γ :
    (γ : V ℓ) (oγ : IsOrd γ) (clγ : closedω γ)
    (x : V ℓ) → ⟨ x ∈ˢ γ ⟩ →
    (n : ℕ) → ⟨ sucIter n x ∈ˢ γ ⟩
sucIter-in-γ γ oγ clγ x x∈ zero = x∈
sucIter-in-γ γ oγ clγ x x∈ (suc n) =
  suc∈γ (sucIter n x) (sucIter-in-γ γ oγ clγ x x∈ n)
  where
  open Closer γ oγ clγ

------------------------------------------------------------------------------
-- THE OBLIGATION.  Exported at the file's top level, at the name the
-- meter reads.  ONE `Lset-mono` application
-- (src/L/Constructible.lagda.md:365) along the membership
-- `sucIter-in-γ` delivers:  stage membership lifts along the iterate's
-- inclusion in γ.  `closedω` and `oγ` enter only through `sucIter-in-γ`.

block∈Lγ :
    (γ : V ℓ) (oγ : IsOrd γ) (clγ : closedω γ)
    (x : V ℓ) → ⟨ x ∈ˢ γ ⟩ →
    (n : ℕ) (b : V ℓ) →
    ⟨ b ∈ˢ Lset (sucIter n x) ⟩ → ⟨ b ∈ˢ Lset γ ⟩
block∈Lγ γ oγ clγ x x∈ n b b∈ =
  Lset-mono {α = γ} {β = sucIter n x} (sucIter-in-γ γ oγ clγ x x∈ n) b∈

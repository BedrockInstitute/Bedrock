{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.751] PROBE.  Finite successor iterates of a member stay inside
-- a closed-omega ordinal:
--
--   sucIter-in-γ :
--       (γ : V ℓ) (oγ : IsOrd γ) (clγ : closedω γ)
--       (x : V ℓ) → ⟨ x ∈ˢ γ ⟩
--       (n : ℕ) → ⟨ sucIter n x ∈ˢ γ ⟩
--
-- `sucIter` is src/L/Ordinal/StageArith.lagda.md:34-36 (zero is the
-- identity; successor is `sucV`).  The successor step is [LJ-1.747]'s
-- `Closer.suc∈γ` (agents/tasks/LJ-1-747/Probe747.agda:85-87),
-- transcribed below at the same trimmed telescope rather than imported:
-- importing Probe747 would drag its numerals and Bound frame into every
-- check of this one for legs this obligation never names, the same
-- trade 747 itself records as its ONE DEVIATION against 737-SPLIT.
-- Lands nothing in src/.  `table-sat` is NOT inhabited.
--
-- ONE Agda process per run, GHCRTS wide caliber, set on the pane by
-- the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-751.Probe751 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import V.Model {ℓ} using ( ∈sucV-elim )
open import L.Constructible {ℓ} using ( IsOrd )
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
-- SECTION 0.  The 747 closer, token for token from
-- agents/tasks/LJ-1-747/Probe747.agda:65-87, which is itself the
-- 737-SPLIT closer (Probe737Split.agda:105-127) with the `hγ : ⟨ isL γ ⟩`
-- argument trimmed.  Transcribed rather than imported: the import route
-- buys a whole probe frame (numerals, Bound) this file cannot use, and
-- the obligation telescope names neither probe.  Same trade, one level
-- up the transcription chain.

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

------------------------------------------------------------------------------
-- THE OBLIGATION.  Exported at the file's top level, at the name the
-- meter reads.  Induction on `n`:  the zero clause is the identity law
-- of `sucIter` (StageArith.lagda.md:35), so the hypothesis passes
-- through; the successor clause computes `sucIter (suc n) x` to
-- `sucV (sucIter n x)` (StageArith.lagda.md:36) and applies the 747
-- step at the previous iterate.  `closedω` enters through `suc∈γ`
-- alone; no `+ω` leg is needed, because the block is finite.

sucIter-in-γ :
    (γ : V ℓ) (oγ : IsOrd γ) (clγ : closedω γ)
    (x : V ℓ) → ⟨ x ∈ˢ γ ⟩ →
    (n : ℕ) → ⟨ sucIter n x ∈ˢ γ ⟩
sucIter-in-γ γ oγ clγ x x∈ zero = x∈
sucIter-in-γ γ oγ clγ x x∈ (suc n) =
  suc∈γ (sucIter n x) (sucIter-in-γ γ oγ clγ x x∈ n)
  where
  open Closer γ oγ clγ

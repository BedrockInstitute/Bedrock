{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.635]  W3, THE WIDEST UNMEASURED TERM: the trichotomy step at
-- the bill's carrier.
--
-- THE QUESTION (brief, W3).  Does `IsOrd (fst κ)` plus the bill's
-- clause `(⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)` give `fst κ ≡ ω` or
-- `⟨ ω ∈ˢ fst κ ⟩`?  The brief's premise 4 names the tool, `ord-tri`
-- (src/L/Ordinal/Linear.lagda.md:136), and flags a CARRIER CROSSING:
-- "`fst κ` is a `V ℓ` and `ord-tri` wants an `S`".  This file measures
-- that crossing.  The answer, stated as a term: THERE IS NO CROSSING.
-- `S` under `open hPropStructure 𝒮ᵥ` IS `V ℓ`, the carrier `IsOrd` and
-- `ord-tri` are stated at, so `ord-tri` applies at `fst κ` by one
-- application ([LJ-1.629] applied it at exactly this grain,
-- agents/tasks/LJ-1-629/Probe629.agda:224-230).  The whole step is:
-- run trichotomy against `ω`, then kill the first case with the bill's
-- own clause.
--
-- TYPE AND TERM.  `tri-above` below is the full step, and it is green:
-- runs/tri-1.out, exit 0.  No hole, no postulate.
--
-- CALIBER.  THE PROGRAM SET GHCRTS ON THIS PANE.  I DID NOT SET IT.
-- ONE AGDA PROCESS AT A TIME.  Cap: TWO MINUTES, set and reported by
-- this task.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-635.runs.Tri {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( ω )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Empty as Empty
open import L.Constructible {ℓ} using ( IsOrd )
open import L.Ordinal {ℓ} using ( ω-ord )
open import L.Ordinal.Linear {ℓ} lem using ( Tri; ord-tri )

open hPropStructure 𝒮ᵥ using ( S; _∈ˢ_ )

-- =====================================================================
-- THE TRICHOTOMY STEP.  `Triω A` is the two live cases of `Tri A ω`
-- once the bill's clause kills `A ∈ˢ ω`: equal to `ω`, or strictly
-- above it.  `tri-above` is the step itself: one `ord-tri` application
-- at `A` (the "crossing" the brief flagged), then the clause kills the
-- first case.  Nothing from SquareLaw is imported: the step does not
-- touch `Init`.
-- =====================================================================

Triω : S → Type (ℓ-suc ℓ)
Triω A = (A ≡ ω) ⊎ ⟨ ω ∈ˢ A ⟩

tri-above : (A : S) → IsOrd A → (⟨ A ∈ˢ ω ⟩ → Empty.⊥) → Triω A
tri-above A oA A∉ω = at (ord-tri A oA ω ω-ord)
  where
    at : Tri A ω → Triω A
    at (inl A∈ω)      = Empty.rec (A∉ω A∈ω)
    at (inr live)     = live

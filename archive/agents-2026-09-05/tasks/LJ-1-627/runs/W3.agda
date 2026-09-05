{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.627]  W3, THE WIDEST UNMEASURED TERM: the code type at the
-- ambient-least ordinal, TYPE ONLY.
--
-- THE SHAPE IS THE CONSUMER'S, not this task's to invent.  The
-- hypothesis [LJ-1.623]'s rows consume is
--
--     (a : S) (oa : IsOrd (fst a))
--     → Σ[ F ∈ S ] InjCode F a (κL a oa)
--
-- (agents/tasks/LJ-1-623/Probe623.agda:140-141, consumed by
-- `codes-at-κL→residue` at :143 and `codes→site` at :145-148).  This
-- file restates that type VERBATIM and nothing else.  `κL` is the
-- sealed ambient-least ordinal
-- (src/L/SquareLawClosed.lagda.md:73-74, from the ambient search
-- `leastOf w lem InjP' nonempty`, src/L/Cardinal.lagda.md:116-117,
-- whose predicate `InjP γ = ∥ Inj γ ∥₁` is the TRUNCATED AMBIENT
-- injection, src/L/Cardinal.lagda.md:66-67), and `InjCode` is the
-- four-conjunct code notion (src/L/Cardinal.lagda.md:223-228).
--
-- TYPE ONLY.  No term of this file proves anything.  No term of this
-- file inhabits the type, and NO TERM OF THIS FILE CARRIES THE BRIEF'S
-- OBLIGATION NAME `codes-at-kappaL`: the name stays out of scope so
-- the program's witness reads the obligation as undelivered, which is
-- the truth of this task's return.
--
-- CALIBER.  THE PROGRAM SET GHCRTS ON THIS PANE.  I DID NOT SET IT.
-- ONE AGDA PROCESS AT A TIME.  Cap: TWO MINUTES, set and reported by
-- this task (runs/w3-1.out).

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open import L.Constructible using ( IsOrd )

module LJ-1-627.runs.W3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open InfinitySet using ( ω )
open import Cubical.Data.Sigma using ( Σ-syntax )
open import L.Ordinal {ℓ} using ( ω-ord )
open import L.Cardinal {ℓ} lem using ( InjCode )
open import L.SquareLawClosed {ℓ} lem ω ω-ord
open import FOL.ZFStructure using ( module hPropStructure )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open hPropStructure 𝒮ʟ using ( S )

-- =====================================================================
-- THE CODE TYPE AT THE AMBIENT-LEAST ORDINAL, TYPE ONLY, capped.
-- The consumer's hypothesis, one spelling
-- (agents/tasks/LJ-1-623/Probe623.agda:140-141).  NOT INHABITED here.
-- =====================================================================

Codes-at-κL : Type (ℓ-suc ℓ)
Codes-at-κL = (a : S) (oa : IsOrd (fst a))
            → Σ[ F ∈ S ] InjCode F a (κL a oa)

{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.738] PROBE.  defat-fill-in-bound-lim, the bounded DefAt fill
-- under closedomega gamma:  the LJ-1.733 obligation re-briefed at the
-- ruled scopes.  Lands nothing in src/.
--
--   THE OBLIGATION (brief LJ-1.738; glyphs kept, except that the
--   V-level membership is renamed ∈ˢᵥ because the L-level one keeps
--   the bare ∈ˢ, the 725-SPLIT disambiguation; and the Powerset-local
--   names toS and DA are resolved at this file's top level):
--     (γ : V ℓ) (oγ : IsOrd γ) (clγ : closedω γ) → ⟨ ω ∈ˢᵥ γ ⟩
--     → (A : S) → ⟨ fst A ∈ Lset γ ⟩
--     → keyS-in-carrier-lim → envSet-in-carrier-lim
--     → Sat-in-carrier-lim
--     → ∀ {n} (w : Fin n) (env : S ^ n)
--     → fst (lookup w env) ≡ fst A
--     → (z : S) (ψ : Formula ⟪ fst A ⟫ 1)
--     → DefOf.defSet (fst A) ψ ≡ fst z
--     → ⟨ (Sat A (toS A ψ) ∷ keyS A ψ ∷ z ∷ env)
--           ⊨ relativize (LsetS γ oγ) (DefBody w) ⟩
--
--   THE CLAUSE (dev/pod/instructions/coder.md, a module hypothesis
--   taken from a predecessor).  Take the type from the probe that
--   typechecked and the verdict from the report;  if the report is
--   NO-GO or names the statement FALSE, stop and say so with
--   file:line, and DO NOT INHABIT the brief's type.  Measured here:
--     keyS-in-carrier-lim      GO, INHABITED.  Probe729.agda:202,
--                              verdict at lj-1.729-report.md:10.
--     envSet-in-carrier-lim    GO, INHABITED.  Probe735.agda:65,
--                              verdict at lj-1.735-report.md:13.
--     Sat-in-carrier-lim       NO-GO, STATED;  the type is priced
--                              FALSE at the full ruled scope.
--                              Probe736.agda:147 (stated, not
--                              inhabited), verdict at
--                              lj-1.736-report.md:13,15 and
--                              review-of-Sat-in-carrier-lim.md:3.
--                              The defect is the ALPHABET:  the type
--                              quantifies over Formula S n, whose
--                              constants range over ALL L-sets, and
--                              the atom clause of `cond` transports a
--                              constant's global membership into
--                              Sat's extension (the 736 kernel,
--                              Probe736.agda:88-135, machine-checked;
--                              the diagonal that would close a
--                              machine-checked ⊥ is unlanded, priced
--                              at far more than a probe by the 736
--                              review).  So the brief's type rests on
--                              a false premise and its only possible
--                              inhabitant is vacuous -- and this
--                              brief's own premise 1 rules that a
--                              vacuous inhabitant is not a GO.
--
--   THE CONSUMPTION SITE (why the false scope is exactly the fed one).
--   The landed unbounded fill concludes at
--   `Sat A (toS ψ) ∷ keyS A ψ ∷ z ∷ γ ⊨ DefBody w`
--   (src/L/Coding/Powerset.lagda.md:500), and `toS ψ` is
--   `mapFo (asConst A) ψ : Formula S 1` -- the fill consumes the Sat
--   bound AT THE WIDE ALPHABET.  The sibling scopes that work (the key
--   bound's `Formula ⟪ fst A ⟫`, the envSet bound) do not reach this
--   conjunct;  only a corrected Sat bound covering the toS image
--   would.
--
--   WHAT IS DELIVERED.  (1) The three hypothesis types, RESTATED, not
--   imported, each with its predecessor's verdict in the comment.
--   (2) The obligation's TYPE, stated with NO inhabitant under its
--   name:  the clause forbids an inhabitant while one module
--   hypothesis is FALSE by its predecessor's report.  No new
--   measurement is re-run here:  the falsity mechanism at this site
--   is the 736 diagonal, which that review prices at far more than a
--   probe, and the clause needs the verdict, not a second refutation.
--   review-of-defat-fill-in-bound-lim.md states the NO-GO.
--
-- NOTHING IS POSTULATED.  No hole in the delivered file.  ONE Agda
-- process per run, GHCRTS = "-A64m -I0 -M2g", the wide caliber, set
-- on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-738.Probe738 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import FOL.Manipulation.Relabelling using ( mapFo )
open import FOL.Manipulation.Relativize using ( relativize )
open import Cubical.Data.Nat using ( ℕ )
open import Cubical.Data.FinData using ( Fin )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( ω )

open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Ordinal.StageArith {ℓ} lem using ( closedω )
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import L.Coding.CodeSet {ℓ} lem using ( keyS )
open import L.Coding.EnvSet {ℓ} lem using ( envSet )
open import L.Coding.Sat {ℓ} lem using ( Sat )
open import L.Coding.Bridge {ℓ} lem using ( asConst )
open import L.Coding.Powerset {ℓ} lem using ( DefBody )
import FOL.Absoluteness

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))

-- The two structures, disambiguated: the V level carries the renamed
-- membership, the constructible level keeps the bare names.
open hPropStructure 𝒮ᵥ using ()
  renaming ( _∈ˢ_ to _∈ˢᵥ_ )
open hPropStructure 𝒮ʟ

-- The obligation's satisfaction is the INNER (L) reading at the
-- identity constant interpretation, the one Powerset's own fill
-- concludes at (AbsL there, AbsL738 here).
module AbsL738 = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL738 using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

-- The Powerset-local toS, resolved at this file's top level (the
-- brief's `toS ψ` at A): the carrier's members coded as constants.
toS : (A : S) → Formula ⟪ fst A ⟫ 1 → Formula S 1
toS A ψ = mapFo (asConst A) ψ

-- =====================================================================
-- SECTION 1.  THE THREE HYPOTHESIS TYPES, RESTATED, NOT IMPORTED.
-- =====================================================================

-- Hypothesis 1, verbatim from the probe that typechecked and
-- INHABITED it, agents/tasks/LJ-1-729/Probe729.agda:202-208.  The
-- verdict is that report's HEAD:  GO on this corrected scope
-- (lj-1.729-report.md:10, :53).

keyS-in-carrier-lim : Type (ℓ-suc ℓ)
keyS-in-carrier-lim =
    (γ : V ℓ) (oγ : IsOrd γ) (clγ : closedω γ)
    (ω∈γ : ⟨ ω ∈ˢᵥ γ ⟩)
    (A : S) (hA : ⟨ fst A ∈ Lset γ ⟩)
    {n : ℕ} (φ : Formula ⟪ fst A ⟫ n)
  → ⟨ keyS A φ ∈ˢ LsetS γ oγ ⟩

-- Hypothesis 2, verbatim from the probe that typechecked and
-- INHABITED it, agents/tasks/LJ-1-735/Probe735.agda:65-71.  The
-- verdict is that report's HEAD:  GO (lj-1.735-report.md:13).

envSet-in-carrier-lim : Type (ℓ-suc ℓ)
envSet-in-carrier-lim =
    (γ : V ℓ) (oγ : IsOrd γ) (clγ : closedω γ)
    → ⟨ ω ∈ˢᵥ γ ⟩
    → (A : S) → ⟨ fst A ∈ Lset γ ⟩
    → (n : ℕ)
    → ⟨ envSet A n ∈ˢ LsetS γ oγ ⟩

-- Hypothesis 3, verbatim from agents/tasks/LJ-1-736/Probe736.agda:
-- 147-153, where the type is STATED, NOT INHABITED.  The verdict is
-- that report's HEAD:  NO-GO, STATED;  the D-10 truth check prices it
-- FALSE at the full ruled scope (lj-1.736-report.md:13, :15;
-- review-of-Sat-in-carrier-lim.md:3).  No inhabitant stands under the
-- name here, and none may:  the clause forbids it.

Sat-in-carrier-lim : Type (ℓ-suc ℓ)
Sat-in-carrier-lim =
    (γ : V ℓ) (oγ : IsOrd γ) (clγ : closedω γ)
    (ω∈γ : ⟨ ω ∈ˢᵥ γ ⟩)
    (A : S) (hA : ⟨ fst A ∈ Lset γ ⟩)
    {n : ℕ} (φ : Formula S n)
  → ⟨ Sat A φ ∈ˢ LsetS γ oγ ⟩

-- =====================================================================
-- SECTION 2.  THE OBLIGATION'S TYPE.  STATED, NOT INHABITED.
--
-- The brief's type, verbatim up to the two resolutions recorded in
-- the header.  The name is exported at the file's top level as a
-- TYPE;  no term stands under it and no postulate supports it.  The
-- clause forbids an inhabitant:  one of the three module hypotheses
-- is FALSE by its predecessor's report, so the brief's type rests on
-- a false premise, an inhabitant could only be vacuous (⊥-elimination
-- through the false hypothesis, or any other route), and the brief's
-- premise 1 says a vacuous inhabitant is not a GO.
-- review-of-defat-fill-in-bound-lim.md states the NO-GO.
-- =====================================================================

defat-fill-in-bound-lim : Type (ℓ-suc ℓ)
defat-fill-in-bound-lim =
    (γ : V ℓ) (oγ : IsOrd γ) (clγ : closedω γ)
  → ⟨ ω ∈ˢᵥ γ ⟩
  → (A : S) → ⟨ fst A ∈ Lset γ ⟩
  → keyS-in-carrier-lim
  → envSet-in-carrier-lim
  → Sat-in-carrier-lim
  → ∀ {n} (w : Fin n) (env : S ^ n)
  → fst (lookup w env) ≡ fst A
  → (z : S) (ψ : Formula ⟪ fst A ⟫ 1)
  → DefOf.defSet (fst A) ψ ≡ fst z
  → ⟨ (Sat A (toS A ψ) ∷ keyS A ψ ∷ z ∷ env)
        ⊨ relativize (LsetS γ oγ) (DefBody w) ⟩

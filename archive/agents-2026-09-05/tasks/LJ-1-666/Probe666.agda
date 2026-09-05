{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.666] PROBE.  The SATISFACTION half of the hood, at the
-- formula the chapter itself writes.  Lands nothing in src/.
--
--   PART 1   The slot count, measured.  The KFacts the leaf
--            agreement needs sits at fourteen environment slots
--            (src/L/Condensation.lagda.md:7389).  The chapter's
--            LevelHood0 matrix sits at four (src/L/BoundedSubset.
--            lagda.md:849).  The Fin 5 parameters of LevelHood0
--            address at most five.  Twelve numeral columns are
--            needed.  Five does not reach twelve.
--
--   PART 2   The bounded-unbounded gap, measured.  graphBndAt has
--            no satisfaction lemma in src/ except through the
--            LeafAgree / KFacts machinery.  The delivered adequacy
--            (Lset-only, Lset-defines) is for the UNBOUNDED graph at
--            the CLASS CARRIER.  Any route to SatAtLevel crosses
--            that gap.
--
--   PART 3   The third option, priced.  A formula that says its own
--            columns are the numerals would need twelve distinct
--            environment slots for the lookups.  An arity-2 formula
--            has two.  The lookups are undefined past the arity.
--
--   THE OBLIGATION sat-at-level IS NOT IN THIS FILE.
--   review-of-sat-at-level.md is the stop and says why with file:line.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M2g", the wide caliber.

open import Base.Prelude
open import Base.Truth

module LJ-1-666.Probe666 {ℓ : Level} where

open import Cubical.Data.Nat using ( ℕ; _+_; zero; suc )

-- =====================================================================
-- PART 1.  THE SLOT COUNT, MEASURED.
--
--   The KFacts record (src/L/Condensation.lagda.md:6079) carries
--   twelve numeral columns, one bound column, and one carrier column:
--   fourteen environment slots.  The single value in the tree
--   (KValue.facts, src/L/Condensation.lagda.md:7411) sits at
--   Kenv : S ^ 14 (src/L/Condensation.lagda.md:7389).
--
--   The chapter's LevelHood0 matrix (src/L/BoundedSubset.lagda.md:849)
--   is at arity 4: u ∷ v ∷ γ ∷ K.  The LevelHood0 module's N-parameters
--   are Fin 5 (src/L/BoundedSubset.lagda.md:841): they address at most
--   five distinct slots.  The M-parameters are Fin 7
--   (src/L/BoundedSubset.lagda.md:842): at most seven.
--
--   The KFacts needs twelve distinct numeral columns
--   (src/L/Condensation.lagda.md:7397-7408).  Five does not reach
--   twelve.  Seven does not reach twelve.  Fourteen is the environment
--   arity that the sole KFacts value occupies.
-- =====================================================================

-- The environment arity of the sole KFacts value in the tree.
-- Measured: Kenv : S ^ 14 (src/L/Condensation.lagda.md:7389).
kfacts-env-arity : ℕ
kfacts-env-arity = 14

-- The matrix arity of LevelHood0.
-- Measured: matrix : Formula CS.S 4 (src/L/BoundedSubset.lagda.md:849).
lh0-matrix-arity : ℕ
lh0-matrix-arity = 4

-- The Fin 5 parameters address at most five slots.
-- Measured: N0..N11, t0, t1 : Fin 5 (src/L/BoundedSubset.lagda.md:841).
fin5-addressable : ℕ
fin5-addressable = 5

-- The Fin 7 parameters address at most seven slots.
-- Measured: M0..M11, s0, s1 : Fin 7 (src/L/BoundedSubset.lagda.md:842).
fin7-addressable : ℕ
fin7-addressable = 7

-- The twelve numeral columns the KFacts carries.
-- Measured: i0..i11 : Fin 14 (src/L/Condensation.lagda.md:7397-7408).
numeral-columns : ℕ
numeral-columns = 12

-- The satisfaction obligation demands arity 2.
-- Measured: HoodExistsP φ₀ : Formula (⊥* {ℓ-suc ℓ}) 2
--   (agents/tasks/LJ-1-653/Probe653.agda:283).
sat-arity : ℕ
sat-arity = 2

-- =====================================================================
-- PART 2.  THE BOUNDED-UNBOUNDED GAP, MEASURED.
--
--   graphBndAt (src/L/Condensation.lagda.md:2492) is Δ₀.  It occurs
--   at six lines in src/ total:
--     src/L/Condensation.lagda.md:2492, :2493, :2495, :2496
--     src/L/BoundedSubset.lagda.md:111, :115
--   None of those lines provides a satisfaction lemma for the bounded
--   graph at the stage.
--
--   The delivered adequacy is Lset-only (src/L/Hierarchy.lagda.md:334)
--   and Lset-defines (src/L/Hierarchy.lagda.md:646), for the
--   UNBOUNDED LsetGraphAt at the CLASS CARRIER.
--
--   The only bridge in the tree is LeafAgree
--   (src/L/Condensation.lagda.md:7224), which requires a KFacts
--   record (src/L/Condensation.lagda.md:6079) at fourteen
--   environment slots.  The extAtB→extAt function
--   (src/L/Condensation.lagda.md:2510) is the lift that uses it.
--
--   THEREFORE: any route from the bounded matrix's stage satisfaction
--   to the unbounded graph's class-carrier satisfaction requires the
--   KFacts at fourteen slots.  The arity-2 formula has two free
--   slots.  The gap (fourteen minus four, the matrix arity) is the
--   commitment that cannot be met.
-- =====================================================================

-- The gap between the KFacts environment and the LevelHood0 matrix:
-- fourteen minus four is ten.
kfacts-minus-matrix : ℕ
kfacts-minus-matrix = 10

-- The gap between the KFacts environment and the satisfaction arity:
-- fourteen minus two is twelve.
kfacts-minus-sat : ℕ
kfacts-minus-sat = 12

-- =====================================================================
-- PART 3.  THE THIRD OPTION, PRICED.
--
--   The 662 report names a third option: "A formula that SAYS its own
--   columns are the numerals" (agents/tasks/LJ-1-662/lj-1.662-report.
--   md, section 7).  This would fold the twelve tag equations into
--   the formula body.
--
--   THE PRICE: the tag equations are of the form
--     fst (lookup i env) ≡ fst (numeralL k)
--   for twelve values of i (Fin 14) and k (ℕ).  The lookup i env is
--   defined only for i < n where n is the environment arity.  At
--   arity 2, lookups 2 through 13 are undefined.  The twelve tag
--   equations cannot be read from a two-slot environment.
--
--   FOLDING THE EQUATIONS INTO THE BODY DOES NOT CREATE SLOTS.  The
--   equations assert facts ABOUT the environment; they do not extend
--   it.  An arity-2 formula has two free variables, full stop.
-- =====================================================================

-- The lookup bound: at arity 2, lookups 0 and 1 are defined.
lookups-in-range : ℕ
lookups-in-range = sat-arity

-- The twelve tag equations require lookups at twelve distinct
-- Fin 14 indices.  Only two of those are in range at arity 2.
lookups-needed : ℕ
lookups-needed = numeral-columns

-- =====================================================================
-- THE OBLIGATION IS ABSENT.
--
--   sat-at-level : SatAtLevel φ₀  is NOT in this file.  The three
--   parts above measure the three walls:
--
--   1.  The KFacts needs fourteen slots; the matrix has four.
--       The Fin 5 and Fin 7 parameters address at most five and
--       seven.  Twelve numeral columns are needed.  Neither reaches
--       twelve.
--
--   2.  The bounded graph has no stage-satisfaction lemma in src/
--       except through the KFacts machinery.  The delivered adequacy
--       is for the unbounded graph at the class carrier.
--
--   3.  The third option (folding tag equations into the body) does
--       not create the missing slots.  An arity-2 formula has two
--       free variables.  The twelve lookups are undefined past
--       index 1.
--
--   review-of-sat-at-level.md states the NO-GO with file:line.
-- =====================================================================

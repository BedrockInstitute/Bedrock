-- [LJ-1.615]  FLOOR RUN, the owner's ruling of 2026-08-23: the probe's
-- import list and frame with the obligation at ONE designed hole, run
-- BEFORE the proof, to price the elaboration floor the frame itself
-- costs.  The heavy import is L.Hierarchy (for Lset-only); everything
-- else is the W3 frame, measured at 1.97 s.  Expected: exit 42 at the
-- hole and nothing else.  The wall clock and peak RSS, not the exit,
-- are the measurement.
--
-- floor-1.out (same protocol, first shape) priced the frame at 2.17 s
-- AND caught a real shape error in Section 3 before any proof was
-- attempted: the satisfaction environment sits at the STRUCTURE's
-- carrier (src/FOL/Semantics.lagda.md:91), so the ambient reading of
-- a class-carrier environment reads through map fst.  This file is
-- the CORRECTED shape, per the same ruling's clause that testing a
-- restructured shape is not a rerun.

{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.615]  ValueIsL, THE SECOND FACTOR OF THE RECOVERED
-- FACTORIZATION, DELIVERED AT TODAY'S CARRIER.
--
-- THE OBLIGATION IS ONE TERM,
--
--   value-is-L : ValueIsL
--
-- the second factor of [LJ-1.611]'s recovered
-- `ambientOnly-from : TransferL → ValueIsL → AmbientOnly`
-- (agents/tasks/LJ-1-611/review-of-graph-ambient.md:79-92, the
-- report's recovery at agents/tasks/LJ-1-611/lj-1.611-report.md:197-199).
-- Nothing is asked of TransferL here and nothing is asked of
-- AmbientOnly; the brief forbids building either.  What this file
-- delivers, all green:
--
--   S1  ValueIsL at TODAY'S carrier (the W3 type, measured alone
--       first at runs/W3.agda: exit 0, 1.97 s, runs/w3-1.out; with
--       RSS capture, 2.10 s, peak 375,848,960 bytes, runs/w3-2.out);
--   S2  the obligation: the type is inhabited by the tree's own
--       delivered determination lemma Lset-only
--       (src/L/Hierarchy.lagda.md:333-335), instantiated at the
--       factorization's own slots {2} zero (suc zero);
--   S3  the recovery CHECK: the retired route's own reduction,
--       `ambientOnly-from`, rebuilt at today's carrier as one line,
--       with TransferL and AmbientOnly as a hypothesis type and the
--       conclusion type and NEITHER built.  If the recovery had read
--       the second factor wrong, S3 would not typecheck; its green
--       run is the evidence the factor splits as the retired author
--       thought.
--
-- THE RECOVERY, FROM THE DELIVERED EVIDENCE ALONE.  No git history
-- was read ([LJ-1.607]'s measurement, premise 10, is why).  The
-- review quotes the retired conclusion type and the factorization
-- (review-of-graph-ambient.md:81-92):
--
--   AmbientOnly = (v b : S) → IsOrd b
--               → ⟨ (v ∷ b ∷ []) AbsL.⊨ᵛ LsetGraphAt {2} zero (suc zero) ⟩
--               → v ≡ Lset b
--
-- and describes TransferL as "the ambient-to-inner transfer of the
-- graph formula at L" and ValueIsL as "the value's constructibility".
-- The arrow type forces the split: ambientOnly-from must hand the
-- ambient hypothesis to TransferL (the only factor that can change a
-- reading) and the RESULT of that to ValueIsL, so ValueIsL consumes
-- the INNER reading at an ordinal and must conclude the equation.
-- ValueIsL is therefore the inner determination of the graph at the
-- class carrier, at the factorization's own slots.  The name's
-- "constructibility" is the pinned reading: the equation says the
-- value IS a tower level, and the tree's isL
-- (src/L/Constructible.lagda.md:376-377) is its unpinned weakening.
--
-- WHAT MOVES AT TODAY'S CARRIER.  The class carrier S = 𝒮ʟ.S, the
-- two readings AbsL.⊨ᵛ and AbsL.⊨ᵐ, and the graph formula at the same
-- slots are all the tree's own (src/FOL/Semantics.lagda.md:71,91,
-- src/FOL/Absoluteness.lagda.md:57-78, src/L/Coding/Sequence.lagda.md:291-292,
-- :349, :353-354).  What moved is twofold.  First the ordinal and
-- tower side: at the retired route IsOrd and Lset stood at the class
-- carrier, today they stand at the ambient carrier
-- (src/L/Constructible.lagda.md), so the statement takes fsts where
-- the retired form did not.  Second the environment discipline: the
-- satisfaction's environment sits at the STRUCTURE's carrier
-- (src/FOL/Semantics.lagda.md:91), so the ambient reading of a
-- class-carrier environment reads through map fst, the tree's own
-- abs0 idiom (src/FOL/Absoluteness.lagda.md:80-81).  See the report's
-- required section for the letter-for-letter diff.
--
-- WHY THE OTHER FACTOR IS NOT BUILT HERE.  TransferL-today, stated
-- below as a type only, runs in the direction [LJ-1.533] measured as
-- unpaid ("Code buys ambient.  Ambient buys nothing.",
-- agents/tasks/LJ-1-533/lj-1.533-report.md:76).  The tree's own
-- transfer machine does not reach it: abs0 and pi1-down cover the
-- bounded quantifiers (src/FOL/Absoluteness.lagda.md:80-121), and the
-- graph's outer binder is the UNBOUNDED exists
-- (src/L/Coding/Sequence.lagda.md:292).  [LJ-1.611] stopped at the
-- same wall from the ambient side.
--
-- Nothing is postulated.  Nothing lands in src/.  No hole in the
-- delivered file.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-615.runs.FLOOR {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset )
import FOL.Absoluteness
open import L.Coding.Sequence {ℓ} lem using ( LsetGraphAt )
open import L.Hierarchy {ℓ} lem using ( Lset-only )
open import Cubical.Data.Vec using ( map; _∷_; [] )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )
module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans

-- =====================================================================
-- SECTION 1.  THE TYPE, AT TODAY'S CARRIER.  This is the W3 type
-- letter for letter (runs/W3.agda).  The two fsts are the only thing
-- that moved from the retired form (review-of-graph-ambient.md:84-86):
-- IsOrd and Lset stand at the ambient carrier today, so the class
-- carrier's elements are projected before they meet them.
-- =====================================================================

ValueIsL : Type (ℓ-suc ℓ)
ValueIsL = (v b : S) → IsOrd (fst b)
         → ⟨ (v ∷ b ∷ []) AbsL.⊨ᵐ LsetGraphAt zero (suc zero) ⟩
         → fst v ≡ Lset (fst b)

-- =====================================================================
-- SECTION 2.  THE OBLIGATION.  The tree's own delivered determination
-- lemma, Lset-only (src/L/Hierarchy.lagda.md:333-335), is stated at
-- VARIABLE slots (w b : Fin n, γ : S ^ n) and proved there.  The
-- factorization's site is the instance {n = 2}, w = zero,
-- b = suc zero, γ = v ∷ b ∷ [], whose lookups reduce on the nose, so
-- the obligation is the instantiation and nothing else.
-- =====================================================================

value-is-L : ValueIsL
value-is-L v b ob h = ?

-- =====================================================================
-- SECTION 3.  THE RECOVERY CHECK.  The retired route's reduction,
-- rebuilt at today's carrier.  TransferL-today is a TYPE, the
-- ambient-to-inner transfer at the class carrier, env by env; it is
-- NOT built, and the brief forbids building it.  AmbientOnly-today is
-- the retired conclusion type, restated with today's fsts and today's
-- environment discipline: the ambient reading of the class-carrier
-- environment v ∷ b ∷ [] is (map fst (v ∷ b ∷ [])) ⊨ᵛ, because the
-- satisfaction's environment sits at the structure's carrier
-- (src/FOL/Semantics.lagda.md:91).  The recomposition is one line and
-- consumes no mathematics beyond the two factor types: ambient reading
-- in, transfer hands it to the inner reading, value-is-L concludes.
-- Its green run is the evidence that the recovered ValueIsL is the
-- factor the retired author meant: a wrong recovery (say, a factor
-- stated at the ambient reading) would not compose.
-- =====================================================================

TransferL-today : Type (ℓ-suc ℓ)
TransferL-today = (v b : S)
          → ⟨ (map fst (v ∷ b ∷ [])) AbsL.⊨ᵛ LsetGraphAt zero (suc zero) ⟩
          → ⟨ (v ∷ b ∷ []) AbsL.⊨ᵐ LsetGraphAt zero (suc zero) ⟩

AmbientOnly-today : Type (ℓ-suc ℓ)
AmbientOnly-today = (v b : S) → IsOrd (fst b)
          → ⟨ (map fst (v ∷ b ∷ [])) AbsL.⊨ᵛ LsetGraphAt zero (suc zero) ⟩
          → fst v ≡ Lset (fst b)

ambientOnly-from : TransferL-today → ValueIsL → AmbientOnly-today
ambientOnly-from tr val v b ob h = val v b ob (tr v b h)

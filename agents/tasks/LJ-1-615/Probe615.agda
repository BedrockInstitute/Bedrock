{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.615]  ValueIsL, THE SECOND FACTOR OF THE RECOVERED
-- FACTORIZATION: THE STOP IS STATED, AND THE NAME IS ABSENT ON
-- PURPOSE.
--
-- THE OBLIGATION WAS ONE TERM,
--
--   value-is-L : ValueIsL
--
-- the second factor of [LJ-1.611]'s recovered
-- `ambientOnly-from : TransferL → ValueIsL → AmbientOnly`
-- (agents/tasks/LJ-1-611/review-of-graph-ambient.md:79-92, the
-- report's recovery at agents/tasks/LJ-1-611/lj-1.611-report.md:197-199).
-- THE ANSWER THIS TASK RETURNS IS THE ONE THE BRIEF FUNDED IN
-- ADVANCE: "IF ValueIsL TURNS OUT TO NEED TransferL, SAY SO AND STOP.
-- That would mean the factorization does not split the way its author
-- thought."  It needs TransferL.  The stop is stated at
-- agents/tasks/LJ-1-615/review-of-value-is-L.md, and the meter will
-- read this file's obligation name as MISSING, exactly as [LJ-1.611]'s
-- meter read its own (lj-1.611-report.md, THE OBLIGATION).
--
-- THE RECOVERY, IN TWO SHAPES, AND WHY THE SECOND IS THE REAL ONE.
-- From [LJ-1.611]'s report ALONE (the arrow type plus the words "the
-- value's constructibility"), the factor reads as the INNER
-- determination, and that reading STATES and even INHABITS at today's
-- carrier: it is the delivered lemma Lset-only
-- (src/L/Hierarchy.lagda.md:333-335) at the factorization's own slots
-- {2} zero (suc zero), landed below as inner-determined.  But that
-- reading is WRONG, and the report itself says so: "Neither factor was
-- delivered there", while the inner Lset-only WAS delivered there
-- ("the delivered inner Lset-only",
-- agents/tasks/archive/L3-32-T70/l3.32-t70-report.md:36-37).  The C-42
-- sweep surfaced the retired route's own task records, which quote the
-- factor's type literally, five times over:
--
--   ValueIsL = (v b : S) → IsOrd b
--            → ⟨ (v ∷ b ∷ []) AbsL.⊨ᵛ LsetGraphAt {2} zero (suc zero) ⟩
--            → ⟨ isL v ⟩
--
-- (agents/tasks/archive/L3-32-T51/l3.32-t51-report.md:55,
-- agents/tasks/archive/L3-32-T144/l3.32-t144-report.md:20,
-- agents/tasks/archive/L3-32-T130/l3.32-t130-report.md:69,
-- agents/tasks/archive/L3-31-IVPROBE/l3.31-ivprobe-report.md:222,
-- agents/tasks/archive/L3-32-T70/l3.32-t70-report.md:38-39).
-- The second factor is the AMBIENT one: the AMBIENT satisfaction of
-- the graph implies the VALUE is constructible.  It was blocked at the
-- retired route on the SAME wall as the first factor ("ValueIsL has
-- the same single blocker", T70:38-39), and Section 4 below rebuilds
-- the retired composition that shows why: the factor's whole job in
-- the proof is to carry the ambient value INTO the class carrier.
--
-- WHAT THIS FILE DELIVERS, ALL GREEN:
--
--   S1  the recovered ValueIsL at TODAY'S carrier (the W3 type,
--       measured alone at runs/W3.agda: exit 0, 1.83 s, peak
--       384,532,480 bytes, runs/w3-3.out), STATED and not inhabited;
--   S2  inner-determined: the inner determination at the
--       factorization's slots, the free lemma the first recovery
--       mistook for the factor;
--   S3  ord-isL: ordinals are constructible, today's two-line
--       delivery of the composition's ordinal input;
--   S4  the retired factorization REBUILT at today's carrier,
--       `ambientOnly-from : TransferL → ValueIsL → AmbientOnly`, one
--       line, with BOTH factors as hypotheses and neither built.  Its
--       green run is the check that the recovery is the factor the
--       retired author meant: the second factor's proof obligation in
--       the composition is exactly the carrier bridge, and the
--       first-shape factor (inner-determined) already sits INSIDE the
--       composition for free.
--
-- WHY THE FACTOR NEEDS TransferL, IN ONE PARAGRAPH.  ValueIsL's
-- hypothesis is the AMBIENT reading at an ARBITRARY ambient
-- environment: every existential of the graph ranges over every
-- ambient set (src/FOL/Semantics.lagda.md:96, the outer binder of the
-- graph itself unbounded at src/L/Coding/Sequence.lagda.md:292).  The
-- conclusion isL v is an inner fact.  The tree's transfer machine
-- covers Delta-0, Sigma-1 and Pi-1 formulas only
-- (src/FOL/Absoluteness.lagda.md:80-121), the graph is none of the
-- three (its approximation conjunct carries unbounded universal
-- quantifiers in the definition itself, src/L/Coding/Sequence.lagda.md:287-292,
-- documented at src/L/Condensation.lagda.md:2461), the bounded
-- restatement's leaf adequacy is conditional on the certificate
-- frame's site facts (src/L/Condensation.lagda.md:7216-7306,
-- [LJ-1.611]'s finding), and the determination lemma is inner-only.
-- Every road from the hypothesis to the conclusion passes through the
-- ambient-to-inner move, which is TransferL's content, and which runs
-- in the direction [LJ-1.533] measured as unpaid
-- (agents/tasks/LJ-1-533/lj-1.533-report.md:76).  The full statement
-- of the stop, with the sweep, is in the review file.
--
-- Nothing is postulated.  Nothing lands in src/.  No hole.  No
-- `value-is-L` name anywhere in this file.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-615.Probe615 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ}
  using ( isL; isL-trans; IsOrd; Lset; Lset→isL )
import FOL.Absoluteness
open import L.Coding.Sequence {ℓ} lem using ( LsetGraphAt )
open import L.Hierarchy {ℓ} lem using ( Lset-only )
open import L.Ordinal {ℓ} using ( suc-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( sucV )
open import Cubical.Data.Vec using ( _∷_; [] )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
module SV = hPropStructure 𝒮ᵥ
module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans

-- =====================================================================
-- SECTION 1.  THE RECOVERED TYPE, AT TODAY'S CARRIER.  Letter for
-- letter the W3 type (runs/W3.agda, runs/w3-3.out).  v and b are
-- ambient sets: the satisfaction's environment sits at the structure's
-- carrier (src/FOL/Semantics.lagda.md:91), and the ambient reading
-- evaluates at the ambient structure with constants by fst
-- (src/FOL/Absoluteness.lagda.md:74-76).  The only change from the
-- retired form is the formula under it: today's rebuilt LsetGraphAt,
-- not the retired chapter's.  STATED, NOT INHABITED: see the header
-- and the review file.
-- =====================================================================

ValueIsL : Type (ℓ-suc ℓ)
ValueIsL = (v b : SV.S) → IsOrd b
         → ⟨ (v ∷ b ∷ []) AbsL.⊨ᵛ LsetGraphAt zero (suc zero) ⟩
         → ⟨ isL v ⟩

-- =====================================================================
-- SECTION 2.  THE FREE LEMMA.  The inner determination at the
-- factorization's own slots: the delivered Lset-only
-- (src/L/Hierarchy.lagda.md:333-335), stated at variable slots and
-- proved there, instantiated at {n = 2}, w = zero, b = suc zero,
-- gamma = v ∷ b ∷ [], whose lookups reduce on the nose.  This is what
-- the first recovery mistook for the factor: it composes with a
-- transfer, but it was free at the retired route and it is free here,
-- so it is not the factor the report says was not delivered.
-- =====================================================================

inner-determined : (v b : AbsL.SM) → IsOrd (fst b)
  → ⟨ (v ∷ b ∷ []) AbsL.⊨ᵐ LsetGraphAt zero (suc zero) ⟩
  → fst v ≡ Lset (fst b)
inner-determined v b ob h = Lset-only zero (suc zero) (v ∷ b ∷ []) h ob

-- =====================================================================
-- SECTION 3.  THE COMPOSITION'S ORDINAL INPUT, DELIVERED TODAY.
-- The retired proof spent an `ord-isL` alongside the free Lset-only
-- ("proved through Lset-only and ord-isL",
-- agents/tasks/archive/L3-32-T144/l3.32-t144-report.md:21).  Today it
-- is two lines: every ordinal sits in the stage above itself
-- (src/L/Ordinal/Stages.lagda.md:434), and a member of a stage is
-- constructible (src/L/Constructible.lagda.md:395-396).
-- =====================================================================

ord-isL : (b : SV.S) → IsOrd b → ⟨ isL b ⟩
ord-isL b ob = Lset→isL (sucV b) (suc-ord ob) b (ord∈Lset-suc b ob)

-- =====================================================================
-- SECTION 4.  THE RETIRED FACTORIZATION, REBUILT AT TODAY'S CARRIER.
-- TransferL is the archived first factor verbatim
-- (agents/tasks/archive/L3-32-T144/l3.32-t144-report.md:19): the
-- ambient reading implies the inner reading at the class carrier, env
-- by env, the pi-1 direction.  AmbientOnly is the archived conclusion
-- (T144:18).  NEITHER IS BUILT, and the brief forbids building them.
-- The recomposition is the retired route's own six-line proof
-- (T130:70): the second factor carries the ambient VALUE into the
-- class carrier, ord-isL carries the ambient ORDINAL, the transfer
-- hands the inner environment to the free inner determination.  Its
-- green run is the evidence that the recovery is right: with the
-- factors as hypotheses the retired arrow typechecks at today's
-- carrier exactly as the report describes it.
-- =====================================================================

TransferL : Type (ℓ-suc ℓ)
TransferL = (v b : AbsL.SM)
         → ⟨ (fst v ∷ fst b ∷ []) AbsL.⊨ᵛ LsetGraphAt zero (suc zero) ⟩
         → ⟨ (v ∷ b ∷ []) AbsL.⊨ᵐ LsetGraphAt zero (suc zero) ⟩

AmbientOnly : Type (ℓ-suc ℓ)
AmbientOnly = (v b : SV.S) → IsOrd b
           → ⟨ (v ∷ b ∷ []) AbsL.⊨ᵛ LsetGraphAt zero (suc zero) ⟩
           → v ≡ Lset b

ambientOnly-from : TransferL → ValueIsL → AmbientOnly
ambientOnly-from tr vl v b ob h =
  Lset-only zero (suc zero) (vL ∷ bL ∷ []) (tr vL bL h) ob
  where
  vL : AbsL.SM
  vL = v , vl v b ob h
  bL : AbsL.SM
  bL = b , ord-isL b ob

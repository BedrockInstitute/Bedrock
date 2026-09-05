{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.569]  Row 1 of `[LJ-1.564]`'s bill: the ambient cardinality at
-- the successor.
--
-- SECTION 1 is W3 and the brief ordered it written FIRST and typechecked
-- ALONE.  Three slices are kept at agents/tasks/LJ-1-569/runs/W3.agda.txt,
-- runs/W3b.agda.txt and runs/W3c.agda.txt, with runs/w3-1.out,
-- runs/w3-2.out and runs/w3-3.out.  They carry the `.txt` suffix
-- because all three are RED by design and `agents/tasks` is on the
-- library's include path (bedrock.agda-lib:2).  ALL THREE ARE NEGATIVE,
-- and w3-3 is the answer: the elaborator names the slot's type.
-- SECTION 2 is the use site, as terms.
-- SECTION 3 is what the site SPENDS, and it is ambient too.
-- SECTION 4 is the direction question the brief asks.
-- SECTION 5 names the demand as one principle.
-- SECTION 6 counts the bill.
--
-- THE OBLIGATION `gch-without-row-1` IS NOT HERE.  It is a NO-GO and
-- agents/tasks/LJ-1-569/review-of-gch-without-row-1.md states it.
--
-- Nothing is postulated.  Nothing lands in src/.  No hole.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-569.Probe569 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd; Lset )
open import L.Cardinal {ℓ} lem using ( IsCardinalL )
open import L.BoundedSubset {ℓ} lem using ( IsCardinal; _↪_ )
open import L.GCH {ℓ} lem using ( GCHStatement; SuccCardL )
open import L.CantorBernstein {ℓ} lem using ( readL )
import FOL.ZFModel
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( ω )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )

module SV = hPropStructure 𝒮ᵥ
module SL = hPropStructure 𝒮ʟ
module ModelL = FOL.ZFModel 𝒮ʟ

import LJ-1-550.Probe550
import LJ-1-558.Probe558
import LJ-1-564.Probe564
module P550 = LJ-1-550.Probe550 {ℓ} lem
module P558 = LJ-1-558.Probe558 {ℓ} lem
module P564 = LJ-1-564.Probe564 {ℓ} lem

-- =====================================================================
-- SECTION 1.  W3.  DOES `gch-from-five` CONSUME ROW 1 AT ALL.
--
--   IT DOES, AND THE ANSWER IS A REFUSAL AND NOT A TERM, so nothing in
--   this section can be green.  The three slices are in runs/.
--
--   SLICE A (runs/W3.agda.txt:48-55, runs/w3-1.out, EXIT=42) binds row 1 and
--   drops it from the argument list of `gch-from-here-sharp`.
--   SLICE B (runs/W3b.agda.txt:49-60, runs/w3-2.out, EXIT=42) drops it at
--   the one place [LJ-1.550] spends it.
--   SLICE C (runs/W3c.agda.txt:58, runs/w3-3.out, EXIT=42) fills the slot
--   with a term of a known wrong type, so the elaborator PRINTS what
--   the slot demands:
--
--     when checking that the expression r3 has type
--     L.BoundedSubset.IsCardinal lem (fst δ)
--
--   Agda 2.8.0 has no unused-binder warning for a term binder, so the
--   brief's "bound but UNUSED" is tested the only way the elaborator
--   can answer it: bind row 1, never mention it, and see whether the
--   term still elaborates.  It does not.
-- =====================================================================

-- =====================================================================
-- SECTION 2.  THE USE SITE.  ONE, AND IT IS Probe564.agda:360.
--
--   `power-into-succ-at` (Probe564.agda:351-361) is the only consumer
--   of row 1 in [LJ-1.564], and its body spends it in one application,
--   `U.member-in-stage (r1 κ δ sc) ...` at Probe564.agda:360.  That
--   `member-in-stage` is agents/tasks/LJ-1-550/Probe550.agda:257-284,
--   and its first argument is `IsCardinal (fst δ)` (:258).
-- =====================================================================

-- THE STEP, WITH THE WHOLE BILL PAID EXCEPT ROW 1, AND ROW 1 LAST.
-- Read the type: rows 2 and 3 are to the left of the arrow that asks
-- for `IsCardinal (fst δ)`, and NOTHING ELSE is.
LandingAt : ModelL.isZFModel → Type (ℓ-suc ℓ)
LandingAt zf =
    (κ δ : SL.S) → IsOrd (fst κ) → (⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)
  → SuccCardL δ κ
  → IsCardinal (fst δ)
  → (y : SL.S) → ⟨ fst y ∈ˢ fst (𝒫 κ) ⟩ → ⟨ fst y ∈ˢ Lset (fst δ) ⟩
  where open ModelL.isZFModel zf using ( 𝒫 )

landing-at : (zf : ModelL.isZFModel) → P550.SqAt → P550.CoHyps → LandingAt zf
landing-at zf r2 r3 κ δ ordκ κ∉ω sc cardδ =
  U.member-in-stage cardδ (r2 κ ordκ) r3
  where
  module U = P550.UseSite zf P564.bounded-subset-theorem (P564.b6-paid zf)
                          P564.b7-paid P564.b8-paid κ δ ordκ κ∉ω sc

-- AND THE TARGET, WITH ROW 1 MOVED TO THE FAR RIGHT.  The other four
-- rows are passed to [LJ-1.564] VERBATIM and in order, so this term is
-- the proof that this task changed exactly one thing.
row-1-is-the-only-gap :
    (zf : ModelL.isZFModel)
  → P550.SqAt → P550.CoHyps → P564.StageCountedCoded → P558.SuccIntoPower zf
  → P550.AmbientCardAtSucc
  → GCHStatement zf
row-1-is-the-only-gap zf r2 r3 b9 b10 r1 =
  P564.gch-from-five zf r1 r2 r3 b9 b10

-- =====================================================================
-- SECTION 3.  WHAT THE SITE SPENDS, AND IT IS AMBIENT TOO.
--
--   [LJ-1.523] measured that `Devlin55.BoundedSubsetAt` spends `cardκ`
--   exactly twice, at src/L/BoundedSubset.lagda.md:1597 and :1601, and
--   both times as `cardκ α α∈κ`.  At the assignment [LJ-1.550] fixed
--   (theorem-κ := `fst δ`, theorem-α := `fst κ`) that application has
--   the type below.
--
--   [LJ-1.550]'s review named a "Route A": restate
--   src/L/BoundedSubset.lagda.md:1386 with the spent form in place of
--   `IsCardinal κ`, "then B5 fills the slot exactly and R1 leaves"
--   (review-of-bridge-without-B5.md:66-69).
--
--   THE TWO TERMS BELOW MEASURE WHAT ROUTE A WOULD BUY, AND IT IS NOT
--   WHAT THIS BRIEF WANTS.  The spent form IS B5, and B5 STILL NAMES
--   AN AMBIENT FUNCTION TYPE: `⟪ fst δ ⟫ ↪ ⟪ fst κ ⟫`.  So Route A
--   weakens the ambient demand and does not remove it.
-- =====================================================================

Row1Spent : Type (ℓ-suc ℓ)
Row1Spent = (κ δ : SL.S) → SuccCardL δ κ → ⟪ fst δ ⟫ ↪ ⟪ fst κ ⟫ → Empty.⊥

-- The spent form is [LJ-1.523]'s B5 on the nose, and `refl` says so.
row-1-spend-is-B5 : Row1Spent ≡ P550.AmbientSpentAtSucc
row-1-spend-is-B5 = refl

-- Row 1 pays it, at the one member `SuccCardL` supplies.  The converse
-- is not a term: the slot is a Π over every member of δ and this gives
-- one.  runs/Neg569.agda.txt:25 with runs/neg-1.out is that measurement,
-- taken at THIS site and not carried over from [LJ-1.550].
row-1-gives-the-spend : P550.AmbientCardAtSucc → Row1Spent
row-1-gives-the-spend r1 κ δ sc = r1 κ δ sc (fst κ) (fst (snd (snd sc)))

-- =====================================================================
-- SECTION 4.  THE DIRECTION.  THE BRIEF ASKS AND THIS ANSWERS.
--
--   Readback (src/L/CantorBernstein.lagda.md:33-38) turns a code into
--   an ambient injection, so it runs AMBIENT → INTERNAL.  The consuming
--   step of section 2 holds `IsCardinalL δ`, from `SuccCardL`'s second
--   conjunct (src/L/GCH.lagda.md:49), and wants `IsCardinal (fst δ)`.
--   THAT IS THE CONVERSE, and src/ has no producer for it: the only
--   `InjCode` producers are src/L/Absorption.lagda.md:614 and
--   src/L/CodedShift.lagda.md:40, and both deliver the single shape
--   `InjCode F (sucʟ γ) γ`.
-- =====================================================================

-- The direction that holds.  Re-measured here and not quoted.
ambient→internal : (μ : SL.S) → IsCardinal (fst μ) → IsCardinalL μ
ambient→internal μ cardμ ν ν∈μ =
  PT.rec Empty.isProp⊥ (λ code → cardμ (fst ν) ν∈μ (readL μ ν code))

-- The direction the site wants.  TYPE ONLY.  This file neither proves
-- it nor refutes it: the brief forbids both.
InternalToAmbient : Type (ℓ-suc ℓ)
InternalToAmbient = (μ : SL.S) → IsCardinalL μ → IsCardinal (fst μ)

-- =====================================================================
-- SECTION 5.  THE DEMAND, NAMED AS ONE PRINCIPLE.
--
--   NOT AN IMPROVEMENT AND NOT OFFERED AS ONE.  `InternalToAmbient` is
--   STRICTLY MORE than row 1: it gives row 1 at every L-cardinal, and
--   row 1 only at a successor pair.  What it buys is a NAME: the route's
--   ambient demand is exactly "an L-cardinal is a cardinal".
-- =====================================================================

row-1-from-the-converse : InternalToAmbient → P550.AmbientCardAtSucc
row-1-from-the-converse w κ δ sc = w δ (fst (snd sc))

gch-from-four-plus-writeback :
    (zf : ModelL.isZFModel)
  → InternalToAmbient
  → P550.SqAt → P550.CoHyps → P564.StageCountedCoded → P558.SuccIntoPower zf
  → GCHStatement zf
gch-from-four-plus-writeback zf w r2 r3 b9 b10 =
  P564.gch-from-five zf (row-1-from-the-converse w) r2 r3 b9 b10

-- =====================================================================
-- SECTION 6.  THE BILL AFTER THIS TASK, COUNTED BY THE ELABORATOR.
--
--   FIVE ROWS, the same five [LJ-1.564] left, in the same order.  This
--   file removed none and added none.  The definition below is an
--   identity at a hand-written type: it does not typecheck if any row
--   moved, changed or left.
-- =====================================================================

bill-after :
    (zf : ModelL.isZFModel)
  → P550.AmbientCardAtSucc → P550.SqAt → P550.CoHyps
  → P564.StageCountedCoded → P558.SuccIntoPower zf
  → GCHStatement zf
bill-after = P564.gch-from-five

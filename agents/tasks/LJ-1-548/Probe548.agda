{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.548]  B9, `StageCountedCoded`, from the coding leg's own code.
--
-- VERDICT: STOP.  The obligation `stage-counted-coded` is NOT written
-- in this file.  The obstruction is
-- agents/tasks/LJ-1-548/review-of-stage-counted-coded.md.
--
-- THIS FILE IS GREEN ON PURPOSE.  A hole would have made every
-- reduction below a claim; green makes each one a measurement.
--
-- TWO STOPS, AND EITHER ONE ALONE IS ENOUGH.
--
--   1.  THE BRIEF'S OWN PRECONDITION FAILS.  The brief says it assumes
--       `[LJ-1.547]` came back GO and orders a stop if it did not land.
--       `agents/tasks/LJ-1-547/` does not exist in this tree and no
--       commit on any branch of this repository ever added it.  So
--       `injcode-assembled` cannot be imported here, and section 3
--       abstracts its SHAPE instead of naming its term.
--
--   2.  THE TYPE WAS ALREADY REFUTED, AND THE REFUTATION IS IN THIS
--       TREE.  `[LJ-1.533]` stated this exact type as
--       `StageCountedCodedᵀ` (agents/tasks/LJ-1-533/Probe533.agda:80-83)
--       and recorded the obstruction at
--       agents/tasks/LJ-1-533/review-of-StageCountedCoded.md, with a
--       corrected target that adds `δ ∈ˢ sucV α₀` and `δ ∉ ω`.  My slot
--       clause forbids inhabiting a type a predecessor's report names
--       false.
--
-- WHAT THIS FILE MEASURES, and none of it needs `[LJ-1.547]`:
--
--   W3.        The type FORMS at B9's frame.  Section 1, type only.  So
--              the row is NOT refuted at the top, and the brief's own
--              fear is not the obstruction.
--
--   THE PAIR.  Section 3 is the shape the coding leg reports
--              delivering, abstracted over its `G` and its `C`.  Its
--              source is an ORDINAL `a`; B9's source is the STAGE
--              `Lset (fst δ)`.  Its target is `C a`, a function OF the
--              source; B9's target is `δ`, named by the consumer.  The
--              pairs differ in BOTH coordinates.
--
--   THE BILL.  Section 4 reduces B9 to exactly two inputs beyond the
--              leg's shape, and inhabits the reduction.  Section 5
--              names which of the two is `[LJ-1.533]`'s wall.
--
-- Nothing is postulated.  There is no hole.  Nothing lands in src/.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-548.Probe548 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd; isL; Lset )
open import L.Cardinal {ℓ} lem using ( InjCode; _↪_ )
open import L.GCH {ℓ} lem using ( InjL )

open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.Data.Sigma using ( _×_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )

-- The L-carrier, B9's carrier (agents/tasks/LJ-1-523/Probe523.agda:259).
module SL = hPropStructure 𝒮ʟ

-- =====================================================================
-- SECTION 1.  W3.  THE WIDEST UNMEASURED TERM, TYPE ONLY.
--
--   The brief ordered this slice written FIRST and typechecked ALONE,
--   and it was: the slice is kept at runs/w3-slice.agda.txt and the run
--   is runs/w3-1.out, exit 0, 1.77 s.
--
--   B9's frame is `(δ Lδ : SL.S) → IsOrd (fst δ) → (fst Lδ ≡ Lset
--   (fst δ))` (agents/tasks/LJ-1-523/Probe523.agda:260-261).  Its
--   conclusion `InjL Lδ δ` unfolds to `∥ Σ[ F ∈ S ] InjCode F Lδ δ ∥₁`
--   (src/L/GCH.lagda.md:37-38).  So the type this slice must form is
--   `InjCode F Lδ δ`, under B9's own two hypotheses.
--
--   IT FORMS.  `InjCode`'s source slot takes any `SL.S` and imposes no
--   ordinal condition of its own (src/L/Cardinal.lagda.md:223-228), so
--   a stage is admissible THERE.  The ordinal condition that blocks
--   this row is not `InjCode`'s: it is the coding leg's, and section 3
--   is where it enters.
-- =====================================================================

W3-code-at-B9-frame :
    (F δ Lδ : SL.S) → IsOrd (fst δ) → (fst Lδ ≡ Lset (fst δ))
  → Type (ℓ-suc ℓ)
W3-code-at-B9-frame F δ Lδ _ _ = InjCode F Lδ δ

-- =====================================================================
-- SECTION 2.  THE OBLIGATION'S TYPE, in the brief's own words.
--
--   NAMED, NOT INHABITED.  It is character for character the type
--   `[LJ-1.533]` stated at Probe533.agda:80-83 and refuted at
--   agents/tasks/LJ-1-533/review-of-StageCountedCoded.md, and character
--   for character row B9 at
--   agents/tasks/LJ-1-523/Probe523.agda:258-261.
-- =====================================================================

StageCountedCodedᵀ : Type (ℓ-suc ℓ)
StageCountedCodedᵀ =
    (δ Lδ : SL.S) → IsOrd (fst δ) → (fst Lδ ≡ Lset (fst δ))
  → InjL Lδ δ

-- =====================================================================
-- SECTION 3.  THE PAIR THE CODING LEG SITS AT, ABSTRACTED.
--
--   `[LJ-1.547]` IS NOT IN THIS TREE, so this file names no term of
--   its and imports no module of its.  What it does instead is state
--   the SHAPE that task's report describes delivering, with the two
--   set-valued operations left as parameters `G` and `C`.  Every
--   consequence below is therefore a fact about the SHAPE and holds
--   whatever `G` and `C` turn out to be, which is the only honest way
--   to reason about a term that has not landed.
--
--   THE SHAPE.  A code whose SOURCE is an ordinal `a`, and whose TARGET
--   is produced FROM that source by `C`.
-- =====================================================================

CodingLegShapeᵀ : (SL.S → SL.S) → (SL.S → SL.S) → Type (ℓ-suc ℓ)
CodingLegShapeᵀ G C = (a : SL.S) → IsOrd (fst a) → InjCode (G a) a (C a)

-- 3.1  THE SOURCE COORDINATE.  To feed B9's source to the shape, the
-- STAGE must be an ORDINAL.  This is the demand, named not inhabited.
SourceDemandᵀ : Type (ℓ-suc ℓ)
SourceDemandᵀ =
    (δ Lδ : SL.S) → IsOrd (fst δ) → (fst Lδ ≡ Lset (fst δ))
  → IsOrd (fst Lδ)

-- 3.2  THE TARGET COORDINATE.  The shape's target is whatever `C`
-- returns; B9's target is the `δ` the consumer named.  This is the
-- demand, named not inhabited.
TargetDemandᵀ : (SL.S → SL.S) → Type (ℓ-suc ℓ)
TargetDemandᵀ C =
    (δ Lδ : SL.S) → IsOrd (fst δ) → (fst Lδ ≡ Lset (fst δ))
  → C Lδ ≡ δ

-- =====================================================================
-- SECTION 4.  THE BILL, AND IT IS INHABITED.
--
--   Given the leg's shape and the two demands, B9 follows and NOTHING
--   ELSE is wanted.  So the two demands ARE the whole distance from the
--   coding leg to B9, and a successor brief may price exactly them.
--
--   THE CONCLUSION IS TRUNCATED and this reduction uses that: `InjL` is
--   `∥ Σ[ F ∈ S ] InjCode F a b ∥₁` (src/L/GCH.lagda.md:37-38), so one
--   `∣_∣₁` closes it.
-- =====================================================================

leg→B9 :
    (G C : SL.S → SL.S)
  → CodingLegShapeᵀ G C → SourceDemandᵀ → TargetDemandᵀ C
  → StageCountedCodedᵀ
leg→B9 G C leg src tgt δ Lδ oδ p =
  ∣ G Lδ
  , subst (λ b → InjCode (G Lδ) Lδ b)
          (tgt δ Lδ oδ p)
          (leg Lδ (src δ Lδ oδ p))
  ∣₁

-- 4.1  AND THE TARGET DEMAND ALONE IS NOT ENOUGH.  Without the source
-- demand the shape cannot be applied at all, because `CodingLegShapeᵀ`
-- takes `IsOrd (fst a)` before it returns anything.  This is that
-- statement: the leg still reaches B9 if the source demand is supplied
-- at the single point it is used.
leg→B9-source-at-a-point :
    (G C : SL.S → SL.S)
  → CodingLegShapeᵀ G C → TargetDemandᵀ C
  → ((δ Lδ : SL.S) → IsOrd (fst δ) → (fst Lδ ≡ Lset (fst δ))
       → IsOrd (fst Lδ))
  → StageCountedCodedᵀ
leg→B9-source-at-a-point G C leg tgt src = leg→B9 G C leg src tgt

-- =====================================================================
-- SECTION 5.  WHICH DEMAND IS `[LJ-1.533]`'s WALL.
--
--   THE SOURCE DEMAND IS NOT THE WALL.  It is a plain falsehood about
--   the tower: a stage is not an ordinal.  `[LJ-1.533]` declined to
--   price a refutation of a statement about a named finite stage,
--   because exhibiting the members of `Lset (# n)` needs the
--   definability machinery (agents/tasks/LJ-1-533/review-of-StageCountedCoded.md,
--   `## D-10`), and I decline it here for the same reason and do not
--   assert it as measured.
--
--   THE WALL IS WHAT REPLACES THE SOURCE DEMAND.  A route that does not
--   pretend the stage is an ordinal must instead cross from the stage
--   to the ordinal, and what the tree delivers for that crossing is
--   AMBIENT: `stage-card-upper` is `⟪ Lset α ⟫ ↪ ⟪ α ⟫`
--   (src/L/StageCardinal.lagda.md:564-565).  Turning THAT into a code
--   is `AmbToCodeᵀ` (agents/tasks/LJ-1-533/Probe533.agda:111-114), and
--   that is the wall, at the SOURCE coordinate and nowhere else.
--
--   This section states the crossing the leg's shape would need.  It is
--   NAMED, NOT INHABITED.
-- =====================================================================

StageToOrdCodeᵀ : Type (ℓ-suc ℓ)
StageToOrdCodeᵀ =
    (δ Lδ : SL.S) → IsOrd (fst δ) → (fst Lδ ≡ Lset (fst δ))
  → ⟪ fst Lδ ⟫ ↪ ⟪ fst δ ⟫
  → ∥ Σ[ F ∈ SL.S ] InjCode F Lδ δ ∥₁

-- 5.1  AND IT CLOSES B9 BY ITSELF, WITHOUT THE CODING LEG AT ALL.
-- Given the ambient injection the chapter delivers, this one crossing
-- is B9.  So the leg's five dispatches are not on this row's critical
-- path: the crossing is.
crossing→B9 :
    StageToOrdCodeᵀ
  → ((δ Lδ : SL.S) → IsOrd (fst δ) → (fst Lδ ≡ Lset (fst δ))
       → ⟪ fst Lδ ⟫ ↪ ⟪ fst δ ⟫)
  → StageCountedCodedᵀ
crossing→B9 cross amb δ Lδ oδ p = cross δ Lδ oδ p (amb δ Lδ oδ p)

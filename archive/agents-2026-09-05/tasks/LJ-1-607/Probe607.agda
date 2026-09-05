{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.607]  THE UNTRUNCATION AT THE BAND, RE-MEASURED AT TODAY'S TREE.
--
-- VERDICT: NO-GO, and the NO-GO answers the brief's question at its
-- root, because the brief's premise about the lost cure is FALSE and
-- the cure it asked about has been FOUND, re-checked COLD at today's
-- tree, and measured NOT TO REACH this payload.  The statement is at
-- agents/tasks/LJ-1-607/review-of-band-untruncation.md.
--
-- The brief's obligation, re-stated:
--
--     band-untruncation : <the untruncation of the data payload
--                           [LJ-1.605] names, at today's tree, or the
--                           term that refutes it here>
--
-- The untruncation is `Untruncation` (agents/tasks/LJ-1-607/runs/
-- W3.agda:62-64), which IS [LJ-1.605]'s `missing-direction-type`
-- (agents/tasks/LJ-1-605/Probe605.agda:177-181) with the payload
-- written out, by `refl` (runs/W3.agda:69-73).  NO TERM OF THIS FILE
-- HAS THAT NAME and no term of this file inhabits that type: on a
-- NO-GO the brief's type is not inhabited.  What this file carries
-- instead is the term the brief's second disjunct asks for, row 2.1
-- below: the untruncation, composed with the supply the tree already
-- holds, IS the square law at the band, as a term.  That term refutes
-- the hope that the untruncation is a cheaper object than the one the
-- campaign has forbidden, and with it the route through this point.
--
--   Section 0.  D-10, BEFORE ANY AGDA: the search, and the finding
--                 that corrects the brief's premise.
--   Section 1.  THE PAYLOAD, and the property it does not have.
--   Section 2.  THE ASSEMBLY: what a working untruncation would have
--                 to be made of, and the one piece the tree lacks.
--   Section 3.  THE VERDICT, in comments, and no further terms.
--
-- NO ROW puts `step`, `branch` or `stage-card-upper` into a conversion
-- problem: [LJ-1.584] measured that one such row does not terminate
-- (agents/tasks/LJ-1-584/runs/w3b-1.out).  They appear in comments
-- and in nothing else.
--
-- CALIBER.  THE PROGRAM SET GHCRTS ON THIS PANE (-A64m -I0 -M2g).
-- I did not set it.  One Agda process at a time.
--
-- W3 IS agents/tasks/LJ-1-607/runs/W3.agda, written FIRST and
-- typechecked ALONE (runs/w3-1.out cold 1.30 s, runs/w3-2.out warm
-- 1.20 s, both GREEN, cap 120 s).  It is IMPORTED below, not
-- restated.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open import L.Constructible using ( IsOrd )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )

open import LJ-1-594.runs.W3 using ( SqParam )

module LJ-1-607.Probe607 {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
  (α₀ : V ℓ) (oα₀ : IsOrd α₀) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import Cubical.Data.Sigma using ( _×_ )
open InfinitySet {ℓ} using ( sucV; ω )

open hPropStructure 𝒮ᵥ using ( S; _∈ˢ_ )
open import L.Ordinal.SquareLaw {ℓ} lem using ( sq )
open import L.SquareLawClosed {ℓ} lem α₀ oα₀ using ( sq-trunc-closed )
open import L.WellOrder.Base {ℓ} using ( leastOf; SWO; IsLeast )
open import LJ-1-607.runs.W3 {ℓ} lem α₀ oα₀


-- ===================================================================
-- SECTION 0.  D-10, BEFORE ANY OTHER AGDA: THE SEARCH.
--
-- 0.1  THE BRIEF'S PREMISE ABOUT THE LOST CURE IS FALSE, and the
--      correction is the first finding of this task.  The brief
--      grepped for `pick-canonical` "in no Agda anywhere: not in
--      `src/`, not in `archive/src/`".  The grep missed the probes'
--      home: the library file puts `agents/tasks` on the include path
--      (`bedrock.agda-lib`, `include: src agents/tasks`), and the
--      term lives at agents/tasks/LJ-1-136/ProbeLJ1136B.agda:114-116,
--      beside its report, exactly where [LJ-1.142] ruled probes live,
--      tracked and never deleted.  The code was never lost.  It was
--      looked for in the wrong directory.
--
-- 0.2  AND IT STILL ELABORATES, COLD, AT TODAY'S TREE.  The interface
--      Agda holds for it was computed 2026-08-19 and only VALIDATED by
--      the warm run (runs/p136-2.out), so the two probe files of
--      [LJ-1.136] and [LJ-1.134] were copied VERBATIM into runs/cold/
--      and re-ascribed from a fresh interface namespace
--      (runs/p136-cold-1.out): GREEN, exit 0, 1.83 s, 327 MB peak,
--      under the program's caliber.  BOTH halves survive: the
--      selection `pick-canonical`, and the discharge `discharge`
--      (agents/tasks/LJ-1-136/ProbeLJ1136B.agda:146-148), which takes
--      the truncated existence of a CONSTRUCTIBLE injective graph and
--      returns an HONEST injection, no truncation left over.
--
-- 0.3  THE INVENTORY OF UNTRUNCATION AT TODAY'S TREE.  One engine
--      eliminates a propositional truncation into data: `leastOf`
--      (src/L/WellOrder/Base.lagda.md:158-161), which turns
--      `∥ Σ a, ⟨ P a ⟩ ∥₁` into `Σ a, IsLeast P a` because
--      `isPropLeastOf` (src/L/WellOrder/Base.lagda.md:136-139) makes
--      the goal a proposition.  Every other `PT.rec` in `src/`
--      eliminates into a proposition (the membership and satisfaction
--      predicates) or into `⊥`; the survey of all 66 files that use
--      it found no exception.  The engine's two consumers at the
--      injection shape show the constraint from both sides:
--      `L.Cardinal`'s `least` (src/L/Cardinal.lagda.md:117) runs it
--      with the predicate `InjP γ = ∥ Inj γ ∥₁ , squash₁`
--      (src/L/Cardinal.lagda.md:66-67), so the LEAST INDEX comes out
--      and the ambient injection STAYS TRUNCATED inside the
--      proposition; [LJ-1.136]'s `Sel` runs it on CODES instead, and
--      only that is why its discharge hands out a function.  Neither
--      consumer delivers an ambient function payload.
--
-- 0.4  WHY THE CURE DOES NOT REACH THIS PAYLOAD.  `Sel.discharge`
--      consumes `Ne = ∥ Σ[ A ∈ Mem (Lset β) ] ⟨ Good A ⟩ ∥₁`
--      (agents/tasks/LJ-1-136/ProbeLJ1136B.agda:98-99): the TRUNCATED
--      EXISTENCE OF A CONSTRUCTIBLE GRAPH, at a bounded stage, with
--      `Good` Ω-valued (agents/tasks/LJ-1-136/ProbeLJ1136B.agda:92-96).
--      The band's supply is `∥ sq δ ∥₁`: the truncated existence of
--      an AMBIENT FUNCTION PACKAGE (runs/W3.agda:46-50), which carries
--      NO Formula, no L-set, no satisfaction and no ordinal grade
--      (agents/tasks/LJ-1-594/runs/W3.agda:42-43).  Between the two
--      sits the bridge: turn an ambient pairing into a constructible
--      graph coding one.  The tree holds no such bridge, and the
--      generator argument that says why is [LJ-1.533]'s, read again
--      at today's lines: the only two producers of an L-element set
--      are `hasSeparationL` (src/L/Axioms/Full.lagda.md:144-146) and
--      `hasReplacementL` (src/L/Axioms/Full.lagda.md:277-280), and
--      BOTH take a `Formula` in their type
--      (agents/tasks/LJ-1-533/review-of-StageCountedCoded.md:107-111).
--      An element of `sq δ` carries no `Formula`, so neither generator
--      can be called on it.  Section 2 states this as a term.
-- ===================================================================


-- ===================================================================
-- SECTION 1.  THE PAYLOAD, AND THE PROPERTY IT DOES NOT HAVE.
--
--   [LJ-1.576] measured the property that lets the CODED side
--   untruncate: `InjCode F a b` is an hProp, four Ω-valued conjuncts
--   (agents/tasks/LJ-1-576/Probe576.agda:77-84).  That is the
--   property of a CODE family, and the band's payload is not a code
--   family: it is a Σ whose first component is a FUNCTION between the
--   member types (src/L/Ordinal/SquareLaw.lagda.md:685-687).  No
--   comparable property is available to it, and rows 1.2 and 1.3
--   below make the demand exact.
-- ===================================================================

-- 1.1  THE TREE'S BAND SUPPLY, at the written-out payload.  This is
--      the supply row W3.4 of [LJ-1.605] re-ascribed here, and the
--      definitional identity runs/W3.agda:53-54 is what makes the
--      ascription elaborate without transport.
band-supply :
    (δ : V ℓ) → ⟨ δ ∈ˢ sucV α₀ ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥) → Payload δ
band-supply = sq-trunc-closed

-- 1.2  THE DIRECT ROUTE, AS A TERM: it is available at a site EXACTLY
--      when the fiber is a proposition, and for nothing less.  The
--      elaborator's own statement of the demand was measured at
--      runs/direct-refused-1.out (exit 42): the trivial candidate for
--      the proposition argument does not check, and no other
--      candidate exists in the tree.  The literature's criterion says
--      the same thing from the other side: split support for a type is
--      equivalent to a weakly constant endomap on it (Kraus, Escardó,
--      Coquand and Altenkirch, Theorem 16, cited at
--      dev/literature/truncation-and-selection.md:155-159), and a
--      weakly constant endomap on `sq δ` IS a canonical selection of
--      one pairing: the very thing whose absence is the question.
direct-route-needs :
    (δ : V ℓ) → isProp (sq δ) → (∥ sq δ ∥₁ → sq δ)
direct-route-needs δ hip h = PT.rec hip (λ p → p) h

-- 1.3  AND THE BAND QUESTION CONTAINS THE SITE QUESTION.  A term of
--      `Untruncation` gives split support at every site of the band,
--      without even consulting the site's truncation hypothesis: the
--      band supply is already a family.  So no reading of the band
--      question is weaker than the site question of 1.2.
band-gives-fiber :
    Untruncation
  → (δ : V ℓ) → ⟨ δ ∈ˢ sucV α₀ ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥)
  → (∥ sq δ ∥₁ → sq δ)
band-gives-fiber u δ d∈ d∉ _ = u band-supply δ d∈ d∉


-- ===================================================================
-- SECTION 2.  THE ASSEMBLY: WHAT A WORKING UNTRUNCATION IS MADE OF.
--
--   Three pieces, and the tree holds two of them.
--
--   THE ENGINE: `leastOf` (src/L/WellOrder/Base.lagda.md:158-161),
--   verified cold at today's tree inside the cure's own file
--   (runs/p136-cold-1.out).
--
--   THE DECODING: from a code the checker can select to the honest
--   pairing it codes.  [LJ-1.136]'s `discharge` IS this piece,
--   assembled with the engine (agents/tasks/LJ-1-136/ProbeLJ1136B.
--   agda:146-148), and it is green today.
--
--   THE BRIDGE: from the AMBIENT truncated pairing the band supply
--   holds, to the CODED truncated existence the engine consumes.  The
--   tree holds no such term, and 0.4's generator argument says no
--   call of either producer of L-elements can build one.
--
--   Row 2.2 assembles the three, GENERICALLY (W2): the carrier, the
--   code family and the two pieces are parameters, and the assembly
--   is one term.  What the row proves is that the bridge is the ONLY
--   missing piece: supply it at any code family the engine can
--   select, and the untruncation exists.
-- ===================================================================

-- 2.1  THE TERM THAT REFUTES IT HERE.  An untruncation, composed with
--      the supply the tree already holds, IS `SqParam α₀`: by
--      [LJ-1.604]'s product identity
--      (agents/tasks/LJ-1-604/Probe604.agda:160-164) that is the
--      untruncated square law at every infinite ordinal of the band,
--      fiber by fiber.  Building `band-untruncation` here would not
--      be cheaper than the square law: it WOULD be the square law,
--      and the campaign has forbidden that dispatch at [LJ-1.593]
--      (agents/tasks/LJ-1-593/review-of-square-coded.md:82-84).
--      This is the circle, closed as a term.
the-circle : Untruncation → SqParam α₀
the-circle u = u band-supply

-- 2.2  THE ASSEMBLY, GENERIC IN THE CODE FAMILY.  Given a carrier
--      with a strict well-order, an Ω-valued code family on it, a
--      BRIDGE from the ambient truncated pairing to the coded
--      truncated existence, and a DECODING from a code to the honest
--      pairing, the site's untruncation exists.  [LJ-1.136]'s `Sel`
--      is this row at `A = Mem (Lset β)`, `P = Good`, with
--      `orderAt β oβ` as the order; the engine call below is the same
--      one `pick` makes (agents/tasks/LJ-1-136/ProbeLJ1136B.agda:
--      105-106).  The bridge premise is the piece no instance has.
route-b-assembles :
    {A : Type (ℓ-suc ℓ)} (w : SWO A) (P : A → hProp ℓ)
  → (δ : V ℓ)
  → (bridge : ∥ sq δ ∥₁ → ∥ Σ[ a ∈ A ] ⟨ P a ⟩ ∥₁)
  → (decode : (a : A) → ⟨ P a ⟩ → sq δ)
  → ∥ sq δ ∥₁ → sq δ
route-b-assembles {A} w P δ bridge decode h =
  decode a pa
  where
  sel : Σ[ a ∈ A ] IsLeast w P a
  sel = leastOf w lem P (bridge h)
  a : A
  a = fst sel
  pa : ⟨ P a ⟩
  pa = fst (snd sel)


-- ===================================================================
-- SECTION 3.  THE VERDICT.
--
--   NO-GO, and the circle is CONFIRMED, by a term.  Row 2.1 proves
--   that the untruncation composed with the tree's own band supply is
--   `SqParam α₀`, the square law at the band; row 1.2 proves the
--   direct route is exactly an `isProp (sq δ)` the tree does not hold
--   and the checker refuses to assume (runs/direct-refused-1.out); row
--   2.2 proves the canonical-selection route reduces to ONE missing
--   piece, the bridge from the ambient pairing to a coded existence,
--   and the bridge is [LJ-1.533]'s generator wall re-read at today's
--   lines (section 0.4).
--
--   THE BRIEF'S QUESTION, ANSWERED.  "Does anything in today's tree
--   do what `pick-canonical` was said to do?"  YES: `pick-canonical`
--   ITSELF, still in the tree at agents/tasks/LJ-1-136/
--   ProbeLJ1136B.agda:114, re-verified COLD at this dispatch
--   (runs/p136-cold-1.out, GREEN, 1.83 s).  The brief's premise that
--   the cure's code does not survive is FALSE, and the finding about
--   the archive is the OPPOSITE of the one the brief expected: the
--   archive's record is FAITHFUL and the CODE IS GREEN; what the
--   search of `src/` and `archive/src/` missed is that probes are
--   tracked under `agents/tasks/`, on the include path.  The cure
--   untruncates the payload it was built for, a CONSTRUCTIBLE graph
--   existence at a bounded stage, and the band's payload is an
--   AMBIENT function package.  The distance between the two is the
--   bridge, and the bridge is the wall.
--
--   WHAT THE NEXT BRIEF NEEDS.  Four tasks route through this point
--   and the fifth arrival measured it: the untruncation at the band
--   is not buildable from the tree's stock, because it IS the square
--   law at the band (row 2.1) and its only assembly route needs a
--   coder for ambient pairings (row 2.2), the object [LJ-1.533]
--   refuted by generator count.  This is a RULING for the owner, not
--   a funding question: no sixth dispatch through this point can
--   close it, on either side.
-- ===================================================================

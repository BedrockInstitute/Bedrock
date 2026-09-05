{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.391] PROBE, attempt 2.  Can `sq` be TRUNCATED?  The collection
-- step, measured.  It runs in agents/tasks/LJ-1-391/ and lands nothing.
-- Attempt 1 closed PARKED after a NO-GO with an incomplete enumeration
-- (dev/pod/audit-2026-08-20.md F8).  This file applies the review
-- (review-of-LJ-1-391-1.md) at the same two obligations.
--
--   OBLIGATION 2, BUILT FIRST AND GREEN.  `sq-collect-suffices`: the
--   collected, UNTRUNCATED family is enough for the one consumer, by
--   instantiating the delivered chapter `L.StageCardinal`
--   (src/L/StageCardinal.lagda.md:15-20) and reading
--   `Upper.stage-card-upper` (src/L/StageCardinal.lagda.md:564-566)
--   under one truncation.  Nothing is re-proved.
--
--   THE DIGEST 2.7 CHECK, GREEN.  `ac-composes`: if the collection
--   (HoTT Book 3.8.1) were paid, the truncated consumer would be
--   served, because `sq-collect-suffices` concludes in `∥_∥₁`, which
--   is a proposition (dev/literature/truncation-and-selection.md:223-232).
--
--   OBLIGATION 1, ATTACKED.  `sq-collect` IS the HoTT Book's axiom of
--   choice 3.8.1 at the band: (∏x ∥Y x∥) → ∥∏x Y x∥
--   (dev/literature/truncation-and-selection.md:223-227).  It is not a
--   new statement.  PART 2 reduces it to `PointwiseUntrunc`.  PART 3
--   shows that residue is equivalent to a `2-Constant` endomap of
--   `sq δ` (C-54, Kraus Theorem 16).  The obligation's body is that
--   reduction with the endomap as the hole.  No weakening, no postulate.
--
-- `α₀` and `oα₀` are parameters of this probe module, copied from the
-- consumer's own telescope.  Nothing below names an ordinal, `ω · 2`,
-- `+ω` or any other site (W2, DD4).

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
open import L.Constructible using ( IsOrd )

module LJ-1-391.Probe391 {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
  (α₀ : V ℓ) (oα₀ : IsOrd α₀) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( Lset )
open import L.Ordinal.SquareLaw {ℓ} lem using ( sq )
open import L.Cardinal {ℓ} lem using ( _↪_ )
import L.StageCardinal
open import LJ-1-319.SqIsSet {ℓ} lem using ( sq-set )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( ω; sucV )
open import Cubical.Foundations.Function using ( 2-Constant )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))

-- =====================================================================
-- PART 1.  `sq-collect-suffices`, THE PAYOFF, BUILT FIRST.
--
--   The consumer takes the family as a MODULE PARAMETER
--   (src/L/StageCardinal.lagda.md:15-20) and spends it at exactly one
--   place (src/L/StageCardinal.lagda.md:283), and its conclusion
--   `stage-card-upper` is UNTRUNCATED data
--   (src/L/StageCardinal.lagda.md:564-566).  The trophy speaks in the
--   merely-grade (src/L/GCH.lagda.md:37-38 and :59-66), so one `∣_∣₁`
--   at the boundary is the whole distance.  This is instantiation, W2's
--   write-once discipline: the mathematics is written once in the
--   chapter, and this probe supplies the parameter.
-- =====================================================================

sq-collect-suffices :
    ((δ : V ℓ) → ⟨ δ ∈ sucV α₀ ⟩ → (⟨ δ ∈ ω ⟩ → Empty.⊥) → sq δ)
  → (α : V ℓ) → IsOrd α → ⟨ α ∈ sucV α₀ ⟩ → (⟨ α ∈ ω ⟩ → Empty.⊥)
  → ∥ ⟪ Lset α ⟫ ↪ ⟪ α ⟫ ∥₁
sq-collect-suffices fam α oα α∈suc infα = ∣ emb α oα α∈suc infα ∣₁
  where
  module SC = L.StageCardinal {ℓ} lem α₀ oα₀ fam

  emb : (α : V ℓ) → IsOrd α → ⟨ α ∈ sucV α₀ ⟩ → (⟨ α ∈ ω ⟩ → Empty.⊥)
      → ⟪ Lset α ⟫ ↪ ⟪ α ⟫
  emb = SC.Upper.stage-card-upper

-- THE DIGEST 2.7 CHECK.  AC (3.8.1) delivers `∥ family ∥₁` and never
-- the family.  The consumer of that truncation is
-- `sq-collect-suffices`, whose goal IS a proposition (`∥_∥₁`), so the
-- pair composes by `PT.rec`.  This is the half the digest says works
-- (dev/literature/truncation-and-selection.md:229-232).  The term takes
-- the collection as an argument so it does not depend on the hole.
ac-composes :
    (col : ((δ : V ℓ) → ⟨ δ ∈ sucV α₀ ⟩ → (⟨ δ ∈ ω ⟩ → Empty.⊥) → ∥ sq δ ∥₁)
         → ∥ ((δ : V ℓ) → ⟨ δ ∈ sucV α₀ ⟩ → (⟨ δ ∈ ω ⟩ → Empty.⊥) → sq δ) ∥₁)
  → ((δ : V ℓ) → ⟨ δ ∈ sucV α₀ ⟩ → (⟨ δ ∈ ω ⟩ → Empty.⊥) → ∥ sq δ ∥₁)
  → (α : V ℓ) → IsOrd α → ⟨ α ∈ sucV α₀ ⟩ → (⟨ α ∈ ω ⟩ → Empty.⊥)
  → ∥ ⟪ Lset α ⟫ ↪ ⟪ α ⟫ ∥₁
ac-composes col h α oα α∈suc infα =
  PT.rec squash₁ (λ fam → sq-collect-suffices fam α oα α∈suc infα) (col h)

-- =====================================================================
-- PART 2.  WHAT `sq-collect` NEEDS, AS A RESIDUE, AND PROVEN SUFFICIENT
-- BY A GREEN TERM.
--
--   The conclusion is itself a truncation, so no consumer downstream of
--   it needs the family as data.  The gap between a pointwise supply
--   and a whole family is exactly ONE untruncation per band ordinal:
--   open `∥ sq δ ∥₁` into `sq δ`, once at each δ.  The residue is
--   stated as a type and never postulated (DD9).
-- =====================================================================

-- THE RESIDUE.  Pointwise split support of `sq` over the band.  Together
-- with the truncation on the outside, this is HoTT Book 3.8.1 (the
-- axiom of choice) at this index type
-- (dev/literature/truncation-and-selection.md:223-227).
PointwiseUntrunc : Type (ℓ-suc ℓ)
PointwiseUntrunc =
  (δ : V ℓ) → ⟨ δ ∈ sucV α₀ ⟩ → (⟨ δ ∈ ω ⟩ → Empty.⊥) → ∥ sq δ ∥₁ → sq δ

-- THE RESIDUE SUFFICES, and the proof is bookkeeping: apply it to the
-- supply at each δ, then truncate the whole family once.
pointwise-collects :
    PointwiseUntrunc
  → ((δ : V ℓ) → ⟨ δ ∈ sucV α₀ ⟩ → (⟨ δ ∈ ω ⟩ → Empty.⊥) → ∥ sq δ ∥₁)
  → ∥ ((δ : V ℓ) → ⟨ δ ∈ sucV α₀ ⟩ → (⟨ δ ∈ ω ⟩ → Empty.⊥) → sq δ) ∥₁
pointwise-collects u h =
  ∣ (λ δ δ∈ infδ → u δ δ∈ infδ (h δ δ∈ infδ)) ∣₁

-- =====================================================================
-- PART 3.  C-54 / DIGEST STEPS 1-3 AND 5.  THE `2-Constant` ENDOMAP.
--
--   Digest checklist (dev/literature/truncation-and-selection.md:287-302):
--   (1) goal a proposition?  `sq-collect`'s conclusion is, so `PT.rec`
--       would apply IF the family were already collected.  The stall is
--       inside the family, at each `sq δ`.
--   (2) is `sq δ` a proposition?  Route A below.  No: it is a Σ whose
--       first component is a function (src/L/Ordinal/SquareLaw.lagda.md:685-687).
--   (3) is the goal a SET, with a `2-Constant` map?  `sq δ` is a set
--       (sq-set, agents/tasks/LJ-1-319/SqIsSet.agda:37-41, imported not
--       copied).  `rec→Set` applies iff a `2-Constant` endomap exists.
--       By `trunc→Set≃` this is necessary as well as sufficient
--       (dev/literature/truncation-and-selection.md:186-190).  Law C-54
--       (dev/LESSONS.md:4448-4456) orders this before a new principle.
--   (5) a weakly constant endomap by any other route is the same
--       obligation (Kraus et al., Theorem 16).
--
--   THE TWO DIRECTIONS ARE GREEN.  Paying the endomap IS paying the
--   residue, so this is not a cheaper target.  It is the same target
--   named by the library's set eliminator.
-- =====================================================================

EndomapAt : Type (ℓ-suc ℓ)
EndomapAt =
  (δ : V ℓ) → ⟨ δ ∈ sucV α₀ ⟩ → (⟨ δ ∈ ω ⟩ → Empty.⊥)
  → Σ[ k ∈ (sq δ → sq δ) ] 2-Constant k

const-gives-pointwise : EndomapAt → PointwiseUntrunc
const-gives-pointwise ck δ δ∈ infδ s =
  PT.SetElim.rec→Set (sq-set δ) (fst (ck δ δ∈ infδ)) (snd (ck δ δ∈ infδ)) s

pointwise-gives-const : PointwiseUntrunc → EndomapAt
pointwise-gives-const u δ δ∈ infδ =
  (λ s → u δ δ∈ infδ ∣ s ∣₁)
  , (λ x y → cong (u δ δ∈ infδ) (squash₁ ∣ x ∣₁ ∣ y ∣₁))

-- ROUTE A, DIGEST STEP 2, AND THE ELIMINATOR'S OWN SIGNATURE SHUTS IT.
-- `PT.rec` opens `∥ sq δ ∥₁` only into a PROPOSITION, and the chapter's
-- own extraction device carries the same demand (`extract`,
-- src/L/StageCardinal.lagda.md:419-420, which takes `pA : isProp A`).
-- The term below is route A complete except for that demand.
prop-gives-pointwise :
    ((δ : V ℓ) → isProp (sq δ)) → PointwiseUntrunc
prop-gives-pointwise pp δ δ∈ infδ s = PT.rec (pp δ) (λ t → t) s

-- And the demand is false in general: `sq δ` is a Σ whose first
-- component is an ambient function
-- (src/L/Ordinal/SquareLaw.lagda.md:685-687), and at any banded ordinal
-- that has one pairing, the flipped pairing is a second: a symmetric
-- reader of the pairings is never injective, the refutation
-- dev/literature/truncation-and-selection.md:307-310 records.  `sq-collect`
-- therefore cannot go through `PT.rec`.  The flip closes `isProp (sq δ)`
-- and nothing else: a `2-Constant` endomap may send pairing and flip
-- to the same element, which is why PART 3 is the live obligation.

-- ROUTE B, DIGEST STEP 4, AND NO CARRIER COVERS THE PAIRINGS.  The
-- tree's one untruncation device for non-propositions is the least-code
-- selection: `leastOf` over an SWO (src/L/WellOrder/Base.lagda.md:158-160),
-- spent as `untruncAt` (agents/tasks/LJ-1-314/CodeUntrunc.agda:57-66).
-- It needs a WELL-ORDERED CARRIER covering the witnesses.  The tree's
-- delivered SWOs well-order ordinal indices, L-stage member codes,
-- products of those, Gödel triples of those, naturals, finite-stage
-- points, limits, names, faithful steps, L-hull carriers, and anything
-- that injects into one of those (`pullOrder`,
-- src/L/Choice/Step.lagda.md:226-242).  None has an ambient function
-- type `⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫` as carrier.  `pullOrder` does not
-- rescue this: with B that function type, the injection into a coded
-- carrier IS the door `[LJ-1.386]` measured.  The literature digest
-- predicts none: a canonical injection needs a well-order on the
-- INJECTIONS, which is what `<_L` supplies classically and an ambient
-- function type does not have
-- (dev/literature/truncation-and-selection.md:335-337).  Building that
-- well-order is building `<_L` at the pairings, and it is the door
-- `[LJ-1.386]` measured, not a step around it.
--
-- THE MERELY-2-CONSTANT DOOR IS ALREADY SHUT.  A merely existing
-- weakly constant endomap is free at every merely inhabited type
-- (agents/tasks/LJ-1-384/Probe384.agda:65-67).  If that sufficed for
-- split support, every type would have it
-- (agents/tasks/LJ-1-384/Probe384.agda:69-73), which the digest's
-- section 2.6 records as refuted.  So digest step 5 does not weaken
-- PART 3: the endomap must arrive as DATA.

-- =====================================================================
-- PART 4.  THE OBLIGATION, ATTACKED THROUGH THE REDUCTION.
--
--   `sq-collect` is HoTT Book 3.8.1 (the axiom of choice) at the band.
--   It is `pointwise-collects` after `const-gives-pointwise`.  The hole
--   below is `EndomapAt`, the C-54 residue, and it is the whole missing
--   principle: no weakening of the statement was tried, and no
--   postulate was added.  The endomap is not refuted: under a global
--   well-order it is classically true.  It is unpaid by this tree's
--   devices, at the generic parameter `α₀`.
-- =====================================================================

sq-collect : ((δ : V ℓ) → ⟨ δ ∈ sucV α₀ ⟩ → (⟨ δ ∈ ω ⟩ → Empty.⊥)
                         → ∥ sq δ ∥₁)
           → ∥ ((δ : V ℓ) → ⟨ δ ∈ sucV α₀ ⟩ → (⟨ δ ∈ ω ⟩ → Empty.⊥)
                          → sq δ) ∥₁
sq-collect h = pointwise-collects (const-gives-pointwise {! EndomapAt !}) h

{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1-605]  ONE UNIFORM PAIRING, BECAUSE THE PRODUCT CARRIES NO
-- COHERENCE.
--
-- VERDICT: NO-GO, and the NO-GO is a RULING, because the uniform
-- supply, if built, IS the untruncated square law at every infinite
-- ordinal of the band, fiber by fiber, and the tree has measured that
-- object four times and forbidden a fourth dispatch on it.  The
-- statement is at agents/tasks/LJ-1-605/review-of-uniform-pairing.md.
--
-- The brief's obligation, re-stated:
--
--     uniform-pairing : <one supply of the band that discharges
--                       every fiber at once>
--
-- which is `SqParam α₀` (agents/tasks/LJ-1-594/runs/W3.agda:26-31).
-- NO TERM OF THIS FILE HAS THAT NAME, and no term of this file has
-- that type as its body: on a NO-GO the brief's type is not
-- inhabited, and this probe carries every row the tree holds, green,
-- so that each row is a measurement and not a claim.
--
--   Section 0.  D-10: the no-coherence check, re-verified at this
--                 site, and the target's truth.
--   Section 1.  THE COVERAGE MAP: what the tree supplies, at which
--                 sites, in which truncation.
--   Section 2.  THE GAP, named as a type, and the loop the gap
--                 closes through: the square law, and B9 behind it.
--   Section 3.  THE VERDICT, in comments, and no further terms.
--
-- NO ROW puts `step`, `branch` or `stage-card-upper` into a
-- conversion problem: [LJ-1.584] measured that one such row does not
-- terminate (agents/tasks/LJ-1-584/runs/w3b-1.out).  They appear in
-- comments and in nothing else.
--
-- CALIBER.  THE PROGRAM SET GHCRTS ON THIS PANE (-A64m -I0 -M2g).
-- I did not set it.  One Agda process at a time.
--
-- W3 IS agents/tasks/LJ-1-605/runs/W3.agda, written FIRST and
-- typechecked ALONE (runs/w3-1.out cold, runs/w3-2.out warm, both
-- GREEN, cap 120 s).  It is IMPORTED below, not restated.

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

module LJ-1-605.Probe605 {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
  (α₀ : V ℓ) (oα₀ : IsOrd α₀) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import Cubical.Data.Sigma using ( _×_ )
open import L.Ordinal.SquareLaw {ℓ} lem using ( sq; Init )
open InfinitySet {ℓ} using ( sucV; ω )

open hPropStructure 𝒮ᵥ using ( S; _∈ˢ_ )
open import LJ-1-605.runs.W3 {ℓ} lem α₀ oα₀


-- ===================================================================
-- SECTION 0.  D-10, BEFORE ANY OTHER AGDA.
-- ===================================================================

-- 0.1  THE NO-COHERENCE CHECK, RE-VERIFIED AT THIS SITE.
--      [LJ-1.604] measured the row (agents/tasks/LJ-1-604/Probe604.
--      agda:160-164); a measured cure does not transfer by analogy,
--      so this probe re-proves it here as a term of its own: the
--      obligation's type is the product over the band of the law
--      chapter's fiber, fiber by fiber, and it is `refl`.  The
--      product carries nothing between two sites: no coherence, no
--      uniformity, no definability.  So the brief's premise that one
--      uniform supply, if it existed, would discharge every fiber at
--      once is CONFIRMED at this site, and section 2 prices what the
--      supply itself is.
no-coherence-at-this-site :
    SqParam α₀
      ≡ ((δ : V ℓ) → ⟨ δ ∈ˢ sucV α₀ ⟩
          → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥) → sq δ)
no-coherence-at-this-site = refl

-- 0.2  THE TARGET'S TRUTH, D-10.  The target is not false in the
--      metatheory: classical set theory proves that at every infinite
--      ordinal α the square α × α is in bijection with α, and the
--      campaign's endpoint is L ⊨ ZFC.  So the uniform supply EXISTS
--      classically at every site of the band.  The question this
--      probe answers is not truth.  It is whether the TREE holds one,
--      and whether building one here would be a new measurement or a
--      fourth dispatch on an object the campaign has already priced.
--      Section 2 answers: the object IS the square law at the band,
--      and the tree has priced it.


-- ===================================================================
-- SECTION 1.  THE COVERAGE MAP: WHAT THE TREE SUPPLIES.
-- ===================================================================

-- 1.1  UNTRUNCATED, AT ONE SITE.  The honest pairing at ω, by the
--      order route, zero arithmetic (src/L/InjChain.lagda.md:100,
--      :184-185).  Re-ascribed at the band fiber in W3, row W3.2.
--      COVERAGE: the single site ω.
--      (W3.supply-ω : sq ω)

-- 1.2  UNTRUNCATED, AT THE INITIAL ORDINALS, and ONLY there.  The
--      via-collapse construction (src/L/Ordinal/SquareLaw.lagda.md:
--      944-954) lands the pair inside the ordinal by the exclusion
--      chase, and the chase closes because an initial ordinal
--      contains no smaller infinite ordinal to land in instead.
--      The chapter's own prose states the restriction (src/L/Ordinal/
--      SquareLaw.lagda.md:14-17): at a non-initial ordinal the honest
--      equivalence needs the least-of transfer, which the chapter
--      does not build.  Re-ascribed in W3, row W3.3.
--      COVERAGE: the sites δ with `Init δ`.
--      (W3.supply-init : (δ : S) → Init δ → sq δ)

-- 1.3  TRUNCATED, AT THE WHOLE BAND.  The `∈-induction`
--      (src/L/SquareLawClosed.lagda.md:325-328) delivers, at every δ
--      of the band with its infinitude clause, a truncated pairing:
--      the WFI descent builds ∥ sq δ ∥₁ from the two untruncated
--      supplies and the truncated descent hypothesis.  Re-ascribed in
--      W3, row W3.4.  The truncation is in the type, and no row of
--      this file removes it.
--      COVERAGE: every site of the band, truncated.
--      (W3.supply-band-truncated :
--           (δ : V ℓ) → ⟨ δ ∈ˢ sucV α₀ ⟩
--           → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥) → ∥ sq δ ∥₁)

-- 1.4  THE COUNT.  THREE supplies are in the tree, and the third is
--      the only one that reaches every site.  The sites it leaves
--      untruncated are exactly the non-initial ordinals of the band:
--      ω is one site, `Init` is the initial ordinals, and a δ of the
--      band that is neither is a non-initial ordinal, at which the
--      tree holds only ∥ sq δ ∥₁.  The measurements behind this
--      count, with their own file:line, are in the report, section
--      THE GAP: [LJ-1.107] (the non-initial witness, PARTIAL),
--      [LJ-1.111] (the truncated chain, GREEN), [LJ-1.114] (the
--      threading wall, REVERTED), all in
--      archive/dev/LJ-dispatch-index.md:183, :187, :190.


-- ===================================================================
-- SECTION 2.  THE GAP, AND THE LOOP IT CLOSES THROUGH.
-- ===================================================================

-- 2.1  WHAT A SUPPLY WOULD BUY.  A term of `SqParam α₀` gives, at
--      every site of the band, the untruncated fiber, and the fiber
--      truncates.  So the obligation implies the truncated band
--      supply.  This row is the inhabited direction, written.
untruncated-buys-truncated :
    (sq-param : SqParam α₀)
  → (δ : V ℓ) → ⟨ δ ∈ˢ sucV α₀ ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥)
  → ∥ sq δ ∥₁
untruncated-buys-truncated sqp δ d∈ d∉ = ∣ sqp δ d∈ d∉ ∣₁

-- 2.2  THE MISSING DIRECTION, NAMED AS A TYPE.  A term of this type
--      is precisely a uniform untruncation of the truncated band
--      supply: from a family of TRUNCATED pairings, at every site of
--      the band, to ONE pairing at every site, untruncated.  No term
--      of this file has this type, and the report, section THE GAP,
--      carries the measurements that say the tree holds none: the
--      payload is data, and a data payload does not come out of a
--      truncated selection
--      (dev/literature/truncation-and-selection.md:146-148), the
--      splitSup criterion is the exact necessary-and-sufficient
--      form of this question (same file, section 2.4), and the tree's
--      own threading attempt of the truncated supply into the live
--      consumer is the wall of [LJ-1.114]
--      (archive/dev/LJ-dispatch-index.md:190).
missing-direction-type : Type (ℓ-suc ℓ)
missing-direction-type =
    ( (δ : V ℓ) → ⟨ δ ∈ˢ sucV α₀ ⟩
        → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥) → ∥ sq δ ∥₁ )
  → SqParam α₀

-- 2.3  THE LOOP.  A term of `SqParam α₀` is, by 0.1, the untruncated
--      square law at every infinite ordinal of the band, and that is
--      not a reduction to the square law: it IS the square law,
--      fiber by fiber, at a grain the campaign has now named.  The
--      campaign's measurements of that object, with file:line in the
--      report:
--
--      [LJ-1.107]  PARTIAL: initial ordinals only; the non-initial
--                  case needs an injection the truncated least-of
--                  witness cannot give (archive/dev/LJ-dispatch-
--                  index.md:183).
--      [LJ-1.111]  the truncated square law holds at EVERY infinite
--                  ordinal, no choice (archive/dev/LJ-dispatch-
--                  index.md:187); the chain is green, the threading
--                  is not.
--      [LJ-1.114]  WALL, route level: the live consumer needs ONE
--                  honest injection and two truncation eliminations
--                  collide (archive/dev/LJ-dispatch-index.md:190).
--      [LJ-1.593]  the square law at the campaign's own spelling
--                  reduces to B9, and the review forbids funding it:
--                  "A fourth dispatch on this object buys nothing"
--                  (agents/tasks/LJ-1-593/review-of-square-coded.md:
--                  82-84).
--      [LJ-1.533]  B9, `StageCountedCoded`
--                  (agents/tasks/LJ-1-564/Probe564.agda:127-130), is
--                  NO-GO: nothing in src/ codes an arbitrary ambient
--                  injection, by a generator argument over the two
--                  producers of L-element sets
--                  (agents/tasks/LJ-1-533/review-of-StageCountedCo
--                  ded.md).
--
--      So the uniform supply needs the square law.  That is the loop
--      the brief names, and per the brief it goes to the
--      mathematician, not to a fifth attempt.


-- ===================================================================
-- SECTION 3.  THE VERDICT.
--
--   NO-GO, AND IT IS A RULING.  The uniform supply, if built, is the
--   untruncated square law at every infinite ordinal of the band:
--   0.1 makes that an identity of types, and W3 re-ascribes the tree's
--   three supplies at exactly that fiber.  The tree holds the law
--   untruncated at ω and at the initial ordinals, and holds the whole
--   band only truncated (section 1); the missing direction is named
--   as a type (2.2) and its measurements are the extraction wall of
--   the law chapter, the threading wall of [LJ-1.114], and the B9
--   NO-GO of [LJ-1.533] behind the reduction of [LJ-1.593].
--
--   WHAT THE BRIEF ASKED, ANSWERED.  "BUILD A PAIRING, DO NOT
--   DESCRIBE sq": the pairing the tree could build WITHOUT the square
--   law does not exist in the tree, and the pairing that would
--   discharge the band IS the square law, so building it here would
--   be a fourth dispatch on an object the campaign has measured four
--   times and forbidden at [LJ-1.593].  I did not inhabit the
--   brief's type, and the statement of the NO-GO is at
--   agents/tasks/LJ-1-605/review-of-uniform-pairing.md.
-- ===================================================================

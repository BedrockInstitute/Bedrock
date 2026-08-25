{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.627]  Code DATA at the ambient-least ordinal.  THE TRUTH OF
-- THE TARGET, MEASURED, and the three rows that locate the wall.
--
-- THE BRIEF'S OBLIGATION, re-stated in the consumer's own shape:
--
--     codes-at-kappaL : <a code, AS DATA and not under a truncation,
--                        at the ambient-least ordinal `κL`>
--
-- The interface is NOT this task's to invent: the consumer is
-- [LJ-1.623]'s pair of rows
-- (agents/tasks/LJ-1-623/Probe623.agda:140-148), whose hypothesis is
--
--     (a : S) (oa : IsOrd (fst a))
--     → Σ[ F ∈ S ] InjCode F a (κL a oa)
--
-- one pair per ambient ordinal, DATA, no truncation.  Section 0
-- states that type VERBATIM and ties it to the alone-typechecked W3
-- (agents/tasks/LJ-1-627/runs/W3.agda:56-58) by one refl.
--
-- NO TERM OF THIS FILE HAS THE NAME `codes-at-kappaL`, and no term of
-- this file inhabits the obligation's type as its body.  The stop is
-- the deliverable: the target is FALSE at the all-a shape, by the same
-- collapse semantics that falsified `AmbientToCoded`
-- (agents/tasks/LJ-1-623/review-of-site-fiber.md:79-83), and Section 3
-- records the one further step this task adds.  What the probe
-- MEASURES, green, is where the obligation parks and what its
-- untruncation would still need:
--
--   Section 0.  The obligation's type, verbatim, tied to W3 by refl.
--   Section 1.  WHAT LEASTNESS BUYS, three rows: the readback at the
--               least pair; the landing row (every coded target sits
--               at or above the ambient-least); and the identity of
--               the obligation with the bridge's hardest instance.
--   Section 2.  THE UNTRUNCATION, TYPE ONLY: truncated codes at κL
--               would become data through a stage-bounded least-code
--               selection the tree does not have at this grain.  The
--               DATA/TRUNCATION distinction is NOT where the wall is.
--   Section 3.  THE TRUTH MEASURE (D-10), in prose with file:line:
--               the collapse instance that falsifies the target, and
--               why the Kraus criterion cannot be the supply.
--
-- CALIBER.  THE PROGRAM SET GHCRTS ON THIS PANE.  I DID NOT SET IT.
-- ONE AGDA PROCESS AT A TIME.  Caps are set and reported per run in
-- `runs/`: the floor was measured BEFORE the final form (the landing
-- row holed), per the heavy-object rule.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open import L.Constructible using ( IsOrd )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )

module LJ-1-627.Probe627 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open InfinitySet using ( ω; sucV )
open import Cubical.Data.Sigma using ( Σ-syntax )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import L.Ordinal {ℓ} using ( ω-ord; suc-ord )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
open import L.Cardinal {ℓ} lem using ( _↪_; InjCode )
open import L.SquareLawClosed {ℓ} lem ω ω-ord
open import L.CantorBernstein {ℓ} lem using ( readL )
open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Model {ℓ} using ( self∈sucV )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )
open hPropStructure 𝒮ʟ using ( S )

import LJ-1-627.runs.W3
module W3 = LJ-1-627.runs.W3 lem

-- =====================================================================
-- SECTION 0.  THE OBLIGATION'S TYPE, in the consumer's exact shape.
--   `κL` is the sealed ambient-least ordinal
--   (src/L/SquareLawClosed.lagda.md:73-74), selected by the ambient
--   search whose predicate is the TRUNCATED AMBIENT injection
--   (`InjP γ = ∥ Inj γ ∥₁, squash₁`, src/L/Cardinal.lagda.md:66-67;
--   the search itself at src/L/Cardinal.lagda.md:116-117).  `InjCode`
--   is the four-conjunct code notion
--   (src/L/Cardinal.lagda.md:223-228).  NOT INHABITED by any row of
--   this file.
-- =====================================================================

Codes-at-κL : Type (ℓ-suc ℓ)
Codes-at-κL = (a : S) (oa : IsOrd (fst a))
            → Σ[ F ∈ S ] InjCode F a (κL a oa)

-- The tie to the alone-typechecked W3: one spelling, not two.
codes-type-is-w3 : Codes-at-κL ≡ W3.Codes-at-κL
codes-type-is-w3 = refl

-- =====================================================================
-- SECTION 1.  WHAT LEASTNESS BUYS, three green rows.
-- =====================================================================

-- 1.1  CODES AT THE LEAST PAIR READ BACK AS AMBIENT INJECTIONS, at
--      every pair, with no truncation anywhere in the witness
--      (`readL`, src/L/CantorBernstein.lagda.md:33-36).  This is
--      [LJ-1.623]'s `codes-at-κL→residue` row re-derived standalone,
--      site-free: the site parameters the consumer carries do not
--      occur in the hypothesis.
codes→ambient : Codes-at-κL
              → (a : S) (oa : IsOrd (fst a))
              → ∥ ⟪ fst a ⟫ ↪ ⟪ fst (κL a oa) ⟫ ∥₁
codes→ambient h a oa = ∣ readL a (κL a oa) (h a oa) ∣₁

-- 1.2  THE LANDING ROW, SITE-FREE: every coded target sits AT OR
--      ABOVE the ambient least cardinal.  A code at γ carries an
--      ambient injection at γ (`readL`), and the ambient search
--      (`leastOf w lem InjP' nonempty`, src/L/Cardinal.lagda.md:116-117)
--      then cannot stop above γ.  This is [LJ-1.623]'s 3.4
--      (agents/tasks/LJ-1-623/Probe623.agda:169-191), which carries
--      no site parameter, restated at this file's frame.
coded-sits-above : (a : S) (oa : IsOrd (fst a)) (γ : S)
                 → IsOrd (fst γ) → ∥ Σ[ F ∈ S ] InjCode F a γ ∥₁
                 → ⟨ fst (κL a oa) ∈ˢ sucV (fst γ) ⟩
coded-sits-above a oa γ oγ h = go (ord-tri (fst κ) oκ (fst γ) oγ)
  where
  κ : S
  κ = κL a oa

  oκ : IsOrd (fst κ)
  oκ = κoL a oa

  amb : ∥ ⟪ fst a ⟫ ↪ ⟪ fst γ ⟫ ∥₁
  amb = PT.map (readL a γ) h

  go : ⟨ fst κ ∈ fst γ ⟩ ⊎ ((fst κ ≡ fst γ) ⊎ ⟨ fst γ ∈ fst κ ⟩)
     → ⟨ fst κ ∈ˢ sucV (fst γ) ⟩
  go (inl κ∈γ) = suc-ord oγ .fst κ∈γ (self∈sucV (fst γ))
  go (inr (inl κ≡γ)) =
    subst (λ w → ⟨ fst κ ∈ˢ sucV w ⟩) κ≡γ (self∈sucV (fst κ))
  go (inr (inr γ∈κ)) =
    Empty.rec (κ-min-atL a oa (fst γ , isL-ord (fst γ) oγ) γ∈κ amb)

-- 1.3  THE IDENTITY ROW: the obligation IS the bridge at its hardest
--      instance.  `BridgeLeast` is [LJ-1.623]'s `AmbientToCoded`
--      (agents/tasks/LJ-1-623/Probe623.agda:157-159) SPECIALIZED to
--      the pair (a, κL a oa): truncated ambient in, truncated code
--      out, AT the ambient-least ordinal.  The tree SUPPLIES the
--      ambient side there (`κ-injL`,
--      src/L/SquareLawClosed.lagda.md:82-84), so `bridge→trunc`
--      reads the bridge instance as the truncated form of the
--      obligation, and `codes→bridge` reads the obligation as the
--      bridge instance, untruncated.  Each direction is one line, and
--      together they say: the DATA this brief wants is exactly what
--      the bridge would buy at κL, and nothing less.
BridgeLeast : Type (ℓ-suc ℓ)
BridgeLeast = (a : S) (oa : IsOrd (fst a))
            → ∥ ⟪ fst a ⟫ ↪ ⟪ fst (κL a oa) ⟫ ∥₁
            → ∥ Σ[ F ∈ S ] InjCode F a (κL a oa) ∥₁

codes→bridge : Codes-at-κL → BridgeLeast
codes→bridge h a oa _ = ∣ h a oa ∣₁

bridge→trunc : BridgeLeast
             → (a : S) (oa : IsOrd (fst a))
             → ∥ Σ[ F ∈ S ] InjCode F a (κL a oa) ∥₁
bridge→trunc br a oa = br a oa (κ-injL a oa)

-- =====================================================================
-- SECTION 2.  THE UNTRUNCATION, TYPE ONLY.  NOT INHABITED by any row
--   of this file or of the tree.  What it would need: the least-code
--   selection (`leastOf`, src/L/WellOrder/Base.lagda.md:158-160) turns
--   truncated code existence into DATA once it may search a stage
--   that covers the codes of ONE pair (the pattern [LJ-1.623]'s
--   comment 3.2 names, agents/tasks/LJ-1-623/Probe623.agda:135-139).
--   No such stage is available here: `isL` is a truncated sup over
--   stages (`isL x = ⋁ S (λ α → ...)`), so a code delivered as an
--   L-element names no stage, and the tree holds no row bounding the
--   stage of the codes at one pair (that is a condensation-scale
--   fact).  The row is MOOT for this task's truth question, because
--   its hypothesis is the bridge instance of 1.3, which the collapse
--   semantics falsifies: untruncing a truncated supply that does not
--   exist supplies nothing.
-- =====================================================================

TruncCodes-at-κL : Type (ℓ-suc ℓ)
TruncCodes-at-κL = (a : S) (oa : IsOrd (fst a))
                 → ∥ Σ[ F ∈ S ] InjCode F a (κL a oa) ∥₁

Trunc→Codes : Type (ℓ-suc ℓ)
Trunc→Codes = TruncCodes-at-κL → Codes-at-κL

-- =====================================================================
-- SECTION 3.  THE TRUTH MEASURE (D-10) AND THE LITERATURE ANSWER, in
--   prose, with file:line for every fact.  No Agda row can carry
--   this: the falsifying semantics is not an object of the tree.
--
-- 3.1  THE COLLAPSE INSTANCE.  [LJ-1.623]'s review fixed the pair: in
--      a classical semantics where the ambient and the constructible
--      cardinality of one pair disagree (a collapse extension at
--      `a = ℵ₁^L`, `b = ω`), "the ambient injection exists and no
--      code does" (agents/tasks/LJ-1-623/review-of-site-fiber.md:79-83).
--      THE ONE FURTHER STEP THIS TASK ADDS: in that same semantics
--      the ambient-least ordinal of `a` IS `b`.  `κL a oa` is the
--      least member of the stage after `a` receiving a TRUNCATED
--      AMBIENT injection from `a`
--      (src/L/Cardinal.lagda.md:116-117, :66-67); the ambient there
--      sees `a` countable, so `ω` receives one, and no finite ordinal
--      receives an injection from an infinite ordinal in any ambient;
--      so the search stops exactly at `ω`.  Codes at `κL a oa` at
--      that `a` are therefore codes at `ω`, which the review measured
--      do not exist.  The obligation is FALSE at the all-a shape.
--
-- 3.2  WHY THE UNTRUNCATION CRITERION IS NOT THE SUPPLY.  Kraus,
--      Escardó, Coquand and Altenkirch, Theorem 16: a type has a
--      weakly constant endomap IFF it has split support, `∥X∥ → X`
--      (dev/literature/truncation-and-selection.md:158-159).  Does
--      the code type at `κL` have a weakly constant endomap?  At the
--      collapse pair the code type is EMPTY, the identity is weakly
--      constant, split support holds vacuously, and the DATA is still
--      absent: Theorem 16 converts a SUPPLIED `∥X∥` into `X`, and the
--      missing input is `∥X∥` itself, which is 1.3's bridge instance.
--      Where the codes of one pair are stage-bounded the tree's own
--      least-code selection IS the normalization (the endomap exists,
--      [LJ-1.623]'s comment 5.3, agents/tasks/LJ-1-623/Probe623.agda:
--      228-242); either way the endomap is not the obstacle.  The
--      full answer is in the report's literature section.
-- =====================================================================

{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1-602]  Clause (iii) of the level-hood certificate: the read in
-- the collapse.
--
-- W3 IS SECTION 1 and the brief ordered it written FIRST and
-- typechecked ALONE.  The slice is agents/tasks/LJ-1-602/runs/W3.agda
-- and its green run is runs/w3-2.out (exit 0, 3.12 s, peak
-- 675,217,408 bytes, under the two-minute cap).  runs/w3-1.out is the
-- record of a run that never started: this macOS has no `timeout`
-- binary, exit 127, no Agda process launched.
--
-- THE FLOOR WAS MEASURED BEFORE ANY PROOF (D-10).  runs/FLOOR.agda
-- states the obligation at a bare hole in this file's own trimmed
-- frame: runs/floor-2.out, exit 42 at the one designed hole, 2.81 s,
-- peak 727,351,296 bytes.  The floor is 0.68 GiB against the 2 GiB
-- cap; the frame is affordable and no heap wall was met anywhere in
-- this task.  runs/floor-1.out is a KILLED run, not a wall: the hole
-- was first put under a lambda with a where-definition and the run
-- was killed at the 200 s time-box with no Agda exit line; that shape
-- is not measured and is not priced.
--
-- THE IMPORT FRAME FOLLOWS [LJ-1.598]'s RESTRUCTURE: this file imports
-- src/ and nothing else, because [LJ-1.578]'s own file walls under the
-- standing wide cap with warm dependencies ([LJ-1.598],
-- runs/chain-578.out, exit 251).  Clause (iii) is therefore TAKEN BY
-- RESTATEMENT, text for text from
-- agents/tasks/LJ-1-578/Probe578.agda:503-510.
--
-- WHAT THIS PROBE LANDS.  The finding is an EQUIVALENCE, both
-- directions as terms: clause (iii) is the CONDENSATION COMMUTE
-- dressed in syntax.  Section 3 derives the commute FROM any
-- inhabitant of clause (iii), and builds clause (iii) FROM the commute
-- at the EQUATION formula, whose satisfaction and uniqueness are free
-- (the [LJ-1.598] equation mechanics, read at the collapse).  So no
-- formula is owed on this clause at all: its whole price is the
-- set-level statement `HS.C.π (Lset δ) ≡ Lset (HS.C.π δ)`, which
-- [LJ-1.477] attacked at a MORE GENERAL type and did not build
-- (lj-1.477-report.md, VERDICT), and which no term in the tree
-- inhabits.  THE OBLIGATION IS NOT INHABITED AND NO NAME
-- `defines-level-across` IS DECLARED HERE.  The stop is stated at
-- agents/tasks/LJ-1-602/review-of-defines-level-across.md.
--
-- Nothing is postulated.  Nothing lands in src/.  No hole.
--
-- CALIBER.  The program set GHCRTS="-A64m -I0 -M2g" on this pane.  I
-- did not set it.  One Agda process at a time.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-602.Probe602 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; con; var; _≐_; ⊥̇ )
open import FOL.Manipulation.Relabelling using ( mapFo )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Collapse {ℓ} using ( isTrans )
open import L.Constructible {ℓ} using ( IsOrd; Lset )
open import L.BoundedSubset {ℓ} lem
  using ( module HullStage; module HullExt; module CollapseIso )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; ∅ )
open import Cubical.Data.Sigma using ( _×_ )
open import Cubical.Data.Vec using ( _∷_; [] )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )
open InfinitySet {ℓ} using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
module SV = hPropStructure 𝒮ᵥ
open SV using ( _∈ˢ_ )

-- =====================================================================
-- THE FRAME.  One hull stage and its collapse, exactly as [LJ-1.578]
-- section 8 instantiated them: the hull M, the extensionality of the
-- hull (HullExt.hullExt, src/L/BoundedSubset.lagda.md:1340), and the
-- satisfaction iso at that carrier (CollapseIso, :321).  Nothing from
-- any probe enters this file.
-- =====================================================================

module Frame (lam : SV.S) (ordλ : IsOrd lam)
             (succλ : (d : SV.S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
             (X : SV.S)
             (X⊆Lλ : (z : SV.S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
             (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  module HS = HullStage lam ordλ succλ X X⊆Lλ ∅∈λ
  module HE = HullExt lam ordλ X X⊆Lλ ∅∈λ
  module CI = CollapseIso HS.M HE.hullExt

  -- ===================================================================
  -- SECTION 1.  W3.  THE WIDEST UNMEASURED TERM, TYPE ONLY, ANSWERED.
  --
  --   The type is runs/W3.agda:75-82 letter for letter: clause (iii)'s
  --   collapse reading alone, the uniqueness conjunct with the
  --   satisfaction conjunct removed.  Its green solo run is
  --   runs/w3-2.out.
  --
  --   AND THE ANSWER IS THE SAME VACUITY [LJ-1.598] MEASURED ON CLAUSE
  --   (i): the conjunct ALONE is free, because an UNSATISFIABLE formula
  --   is vacuously unique.  `mapFo CI.I.g ⊥̇` is `⊥̇` definitionally
  --   (src/FOL/Manipulation/Relabelling.lagda.md:63), satisfaction of
  --   `⊥̇` is the algebra's `⊥` (src/FOL/Semantics.lagda.md:99), and
  --   `⟨ ⊥ ⟩` is `⊥*` (src/Base/Truth.lagda.md:121).  THE WEIGHT OF
  --   CLAUSE (iii) IS THE CONJUNCTION, and the conjunction is measured
  --   in section 3: it is the commute.
  -- ===================================================================

  OnlyAcross : Type (ℓ-suc ℓ)
  OnlyAcross =
    (δ : SV.S) (δ∈M : ⟨ δ ∈ˢ HS.M ⟩) → IsOrd (HS.C.π δ)
    → (Lδ∈M : ⟨ Lset δ ∈ˢ HS.M ⟩)
    → Σ[ φ ∈ Formula CI.I.SM 1 ]
        ((b : CI.I.SPM) → ⟨ (b ∷ []) CI.I.⊨ᵖᵐ mapFo CI.I.g φ ⟩
         → fst b ≡ Lset (HS.C.π δ))

  only-across-vacuous : OnlyAcross
  only-across-vacuous δ δ∈M oπδ Lδ∈M = ⊥̇ , λ b h → Empty.rec* h

  -- ===================================================================
  -- SECTION 2.  CLAUSE (iii), TAKEN BY RESTATEMENT AND NOT BY IMPORT.
  --
  --   The text is [LJ-1.578]'s own (Probe578.agda:503-510), with its
  --   `BChain` frame's module openings made explicit here.  Every name
  --   resolves against the same src/ definitions that probe
  --   instantiated: the hull stage, its extensionality, the collapse
  --   iso, the relabelling.
  -- ===================================================================

  DefinesLevelAcross : Type (ℓ-suc ℓ)
  DefinesLevelAcross =
    (δ : SV.S) (δ∈M : ⟨ δ ∈ˢ HS.M ⟩) → IsOrd (HS.C.π δ)
    → (Lδ∈M : ⟨ Lset δ ∈ˢ HS.M ⟩)
    → Σ[ φ ∈ Formula CI.I.SM 1 ]
        ( ⟨ ((Lset δ , Lδ∈M) ∷ []) CI.I.⊨ᵐ φ ⟩
        × ((b : CI.I.SPM) → ⟨ (b ∷ []) CI.I.⊨ᵖᵐ mapFo CI.I.g φ ⟩
           → fst b ≡ Lset (HS.C.π δ)) )

  -- the body at one index, and the identity that says it is clause (iii)
  Body : (δ : SV.S) → ⟨ Lset δ ∈ˢ HS.M ⟩ → Type (ℓ-suc ℓ)
  Body δ Lδ∈M =
    Σ[ φ ∈ Formula CI.I.SM 1 ]
      ( ⟨ ((Lset δ , Lδ∈M) ∷ []) CI.I.⊨ᵐ φ ⟩
      × ((b : CI.I.SPM) → ⟨ (b ∷ []) CI.I.⊨ᵖᵐ mapFo CI.I.g φ ⟩
         → fst b ≡ Lset (HS.C.π δ)) )

  clause-iii-from-body
    : ( (δ : SV.S) (δ∈M : ⟨ δ ∈ˢ HS.M ⟩) → IsOrd (HS.C.π δ)
        → (Lδ∈M : ⟨ Lset δ ∈ˢ HS.M ⟩) → Body δ Lδ∈M )
    → DefinesLevelAcross
  clause-iii-from-body f = f

  -- ===================================================================
  -- SECTION 3.  THE FINDING.  CLAUSE (iii) IS THE COMMUTE, BOTH
  -- DIRECTIONS, AS TERMS.
  --
  --   THE COMMUTE is [LJ-1.578]'s `Facts.LevelsCommute` at one δ
  --   (Probe578.agda:126-128), the condensation's core.  [LJ-1.578]
  --   paid one direction of the equivalence and called it `b-from-across`
  --   (Probe578.agda:513-524), at the price of a Fact A to supply the
  --   level's membership; clause (iii) HYPOTHESIZES that membership, so
  --   the derivation below needs no Fact A.
  --
  --   THE OTHER DIRECTION IS THE EQUATION ROUTE.  At the constant the
  --   clause itself certifies, `var zero ≐ con (Lset δ , Lδ∈M)`,
  --   satisfaction is `refl` and uniqueness is path equality read at
  --   the restricted structure (src/FOL/ZFStructure.lagda.md:148 on
  --   top of :82; src/FOL/Semantics.lagda.md:93).  So the ONLY thing
  --   the clause wants beyond free syntax is the commute, and the
  --   commute gives the clause outright.  NO GRAPH FORMULA, NO
  --   DETERMINATION, NO WITNESS SELECTION IS OWED ON THIS CLAUSE.
  -- ===================================================================

  -- the commute, at clause (iii)'s own hypotheses
  Commute : Type (ℓ-suc ℓ)
  Commute =
    (δ : SV.S) (δ∈M : ⟨ δ ∈ˢ HS.M ⟩) → IsOrd (HS.C.π δ)
    → (Lδ∈M : ⟨ Lset δ ∈ˢ HS.M ⟩)
    → HS.C.π (Lset δ) ≡ Lset (HS.C.π δ)

  -- DIRECTION ONE.  Any inhabitant of clause (iii) IS the commute: the
  -- image of the certified level satisfies the mapped formula
  -- (`iso-inv`, src/L/BoundedSubset.lagda.md:195), so uniqueness at
  -- that image is the commute.  `fst (CI.I.g m)` is `HS.C.π (fst m)`
  -- by unfolding `g` (:167) and `p` (:325).
  across-gives-commute : DefinesLevelAcross → Commute
  across-gives-commute da δ δ∈M oπδ Lδ∈M =
    snd (snd (da δ δ∈M oπδ Lδ∈M)) (CI.I.g (Lset δ , Lδ∈M)) sat
    where
    φ : Formula CI.I.SM 1
    φ = fst (da δ δ∈M oπδ Lδ∈M)
    sat : ⟨ (CI.I.g (Lset δ , Lδ∈M) ∷ []) CI.I.⊨ᵖᵐ mapFo CI.I.g φ ⟩
    sat = CI.I.iso-inv 1 φ ((Lset δ , Lδ∈M) ∷ [])
            (fst (snd (da δ δ∈M oπδ Lδ∈M)))

  -- DIRECTION TWO.  The equation formula, and its two free halves.
  eqA : (δ : SV.S) (Lδ∈M : ⟨ Lset δ ∈ˢ HS.M ⟩) → Formula CI.I.SM 1
  eqA δ Lδ∈M = var zero ≐ con (Lset δ , Lδ∈M)

  eq-sat : (δ : SV.S) (Lδ∈M : ⟨ Lset δ ∈ˢ HS.M ⟩)
         → ⟨ ((Lset δ , Lδ∈M) ∷ []) CI.I.⊨ᵐ eqA δ Lδ∈M ⟩
  eq-sat δ Lδ∈M = refl

  eq-uniq : (δ : SV.S) (Lδ∈M : ⟨ Lset δ ∈ˢ HS.M ⟩) (b : CI.I.SPM)
          → ⟨ (b ∷ []) CI.I.⊨ᵖᵐ mapFo CI.I.g (eqA δ Lδ∈M) ⟩
          → fst b ≡ HS.C.π (Lset δ)
  eq-uniq δ Lδ∈M b h = h

  commute-gives-across : Commute → DefinesLevelAcross
  commute-gives-across cm =
    clause-iii-from-body (λ δ δ∈M oπδ Lδ∈M → go δ δ∈M oπδ Lδ∈M (cm δ δ∈M oπδ Lδ∈M))
    where
    go : (δ : SV.S) (δ∈M : ⟨ δ ∈ˢ HS.M ⟩) → IsOrd (HS.C.π δ)
       → (Lδ∈M : ⟨ Lset δ ∈ˢ HS.M ⟩)
       → HS.C.π (Lset δ) ≡ Lset (HS.C.π δ) → Body δ Lδ∈M
    go δ δ∈M oπδ Lδ∈M e =
      eqA δ Lδ∈M , eq-sat δ Lδ∈M , λ b h → eq-uniq δ Lδ∈M b h ∙ e

  -- ===================================================================
  -- SECTION 4.  WHAT THE COLLAPSE CHANGES, AS TERMS AND NOT AS PROSE.
  --
  --   GIVES: the collapse's carrier is TRANSITIVE
  --   (`HS.C.πX-trans`, src/V/Collapse.lagda.md:89), and the hull's is
  --   not (HullStage delivers no transitivity of M).  TAKES AWAY: the
  --   collapse reading of a MAPPED formula is the hull reading, both
  --   directions (`iso-inv` and `iso-inv-bwd`,
  --   src/L/BoundedSubset.lagda.md:195 and :250), so for mapped
  --   formulas the collapse decides EXACTLY what the hull decides.  The
  --   two terms below are those facts at this site.
  -- ===================================================================

  -- the transfer, at one free variable (the middle leg [LJ-1.578]
  -- section 4 named; here at this file's own instance)
  iso-inv-at-the-site : (φ : Formula CI.I.SM 1) (q : CI.I.SM)
                      → ⟨ (q ∷ []) CI.I.⊨ᵐ φ ⟩
                      → ⟨ (CI.I.g q ∷ []) CI.I.⊨ᵖᵐ mapFo CI.I.g φ ⟩
  iso-inv-at-the-site φ q = CI.I.iso-inv 1 φ (q ∷ [])

  -- every satisfier of the collapse reading IS the image of a satisfier
  -- of the hull reading: surjectivity (:175, `surj'`) plus the backward
  -- transfer.  This is why the uniqueness conjunct of clause (iii)
  -- ranges over exactly the collapse's images, and why no formula-side
  -- content can be gained by reading in the collapse.
  collapse-satisfiers-lift
    : (φ : Formula CI.I.SM 1) (b : CI.I.SPM)
    → ⟨ (b ∷ []) CI.I.⊨ᵖᵐ mapFo CI.I.g φ ⟩
    → ∥ Σ[ q ∈ CI.I.SM ]
         ( ⟨ (q ∷ []) CI.I.⊨ᵐ φ ⟩ × (CI.I.g q ≡ b) ) ∥₁
  collapse-satisfiers-lift φ b h = PT.map go (CI.I.surj' b)
    where
    go : Σ[ q ∈ CI.I.SM ] (CI.I.g q ≡ b)
       → Σ[ q ∈ CI.I.SM ]
           ( ⟨ (q ∷ []) CI.I.⊨ᵐ φ ⟩ × (CI.I.g q ≡ b) )
    go (q , e) =
      q , ( CI.I.iso-inv-bwd 1 φ (q ∷ [])
            ( subst (λ w → ⟨ w CI.I.⊨ᵖᵐ mapFo CI.I.g φ ⟩)
                (sym (cong (_∷ []) e)) h )
          , e )

  -- the one structural fact the collapse gives and the hull lacks
  image-trans : isTrans HS.C.πX
  image-trans = HS.C.πX-trans

  -- ===================================================================
  -- SECTION 5.  THE RESIDUE, NAMED.
  --
  --   The corrected target for this clause is `Commute` above: a
  --   SET-LEVEL statement, not a formula statement.  It is unbuilt.
  --   [LJ-1.477] attacked the MORE GENERAL type without this clause's
  --   two hypotheses (`PiCommuteLset`, Probe477.agda:100-102) and
  --   stopped at the join of the two computation laws
  --   (lj-1.477-report.md, VERDICT), naming as candidate obstruction a
  --   NON-ORDINAL collapse; this clause's hypothesis
  --   `IsOrd (HS.C.π δ)` excludes exactly that case, so the clause
  --   stands or falls with the commute at ordinal collapse.  Nothing
  --   else is owed: sections 3 and 4 are the whole distance between the
  --   clause and the commute.
  -- ===================================================================

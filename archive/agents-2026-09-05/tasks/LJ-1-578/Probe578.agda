{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.578]  Build `CoHyps`, at the price its predecessor measured.
--
-- W3 IS SECTION 1 and the brief ordered it written FIRST and typechecked
-- ALONE.  The slice is agents/tasks/LJ-1-578/runs/W3.agda; its runs are
-- runs/w3-1.out (exit 42, the module name) and runs/w3-2.out (exit 0).
--
-- Nothing is postulated.  Nothing lands in src/.  No hole.
--
-- CALIBER.  The program set GHCRTS="-A64m -I0 -M8g" on this pane.  I did
-- not set it.  One Agda process at a time.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-578.Probe578 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd; Lset )
open import L.GCH {ℓ} lem using ( GCHStatement )
open import L.BoundedSubset {ℓ} lem
  using ( IsCardinal; _↪_; module HullStage )
import FOL.ZFModel
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; _∪_; ⁅_⁆s; ∅ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open InfinitySet {ℓ} using ( ω; sucV )
open import Cubical.Data.Sigma using ( _×_ )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

-- THE PREDECESSORS, BY THE TYPE EACH ONE DELIVERED (coder clause,
-- owner 2026-08-20).  [LJ-1.570] is GO on its own obligation
-- (lj-1.570-report.md:6) and its stop is about `CoHyps`, not about the
-- terms this file imports.  [LJ-1.564] is GO (lj-1.564-report.md:3).
-- [LJ-1.550] is NO-GO on its own obligation only; `CoHyps` is a TYPE in
-- its green module.
import LJ-1-550.Probe550 {ℓ} lem as P550
import LJ-1-558.Probe558 {ℓ} lem as P558
import LJ-1-564.Probe564 {ℓ} lem as P564
import LJ-1-570.Probe570 {ℓ} lem as P570

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
module SV = hPropStructure 𝒮ᵥ
module ModelL = FOL.ZFModel 𝒮ʟ
open SV using ( _∈ˢ_ )

-- =====================================================================
-- SECTION 1.  W3.  THE WIDEST UNMEASURED TERM, TYPE ONLY.
--
--   The brief names it "whichever of `levelIn` and `cover` [LJ-1.570]
--   marked hardest".  IT IS `cover`, on that report's own two marks:
--   lj-1.570-report.md:81-83 (`cover` asks the SAME adequacy as
--   `levelIn` PLUS a least-witness selection) and :86-88 (`cover` is
--   general at all three of its consumers, where `levelIn` has one and
--   that one was weakened to successors, Probe570.agda:360-365).
--
--   The type below is `Probe570.agda:84-96` letter for letter.  I took
--   it rather than restating it, and section 7 says what I took and
--   from where.
-- =====================================================================

CoverAt : Type (ℓ-suc ℓ)
CoverAt =
    (κ : SV.S) (ordκ : IsOrd κ) (cardκ : IsCardinal κ)
    (κ∉ω : ⟨ κ ∈ˢ ω ⟩ → Empty.⊥)
    (α : SV.S) (ordα : IsOrd α) (α∈κ : ⟨ α ∈ˢ κ ⟩)
    (α∉ω : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
    (sq : P550.SqLaw α)
    (x : SV.S) (x⊆Lα : (z : SV.S) → ⟨ z ∈ˢ x ⟩ → ⟨ z ∈ˢ Lset α ⟩)
    (absorbs : ⟪ Lset α ∪ ⁅ x ⁆s ⟫ ↪ ⟪ Lset α ⟫)
    (lam : SV.S) (ordλ : IsOrd lam) (α∈λ : ⟨ α ∈ˢ lam ⟩)
    (succλ : (d : SV.S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
    (x∈Lλ : ⟨ x ∈ˢ Lset lam ⟩)
  → P550.Tele.Cover κ ordκ cardκ κ∉ω α ordα α∈κ α∉ω sq x x⊆Lα absorbs
      lam ordλ α∈λ succλ x∈Lλ

-- And it IS [LJ-1.570]'s, not a lookalike.
w3-is-570s : CoverAt → P570.CoverAt
w3-is-570s c = c

-- =====================================================================
-- SECTION 2.  D-10, AND IT IS A SHARPENING OF [LJ-1.570]'s INVENTORY.
--
--   [LJ-1.570] reduced `CoHyps` from SEVENTEEN slots to SIX
--   (Probe570.agda:188-194), and stopped with two whole statements
--   owing: `LevelInH` and `CoverH` (Probe570.agda:154-162).  ITS
--   INVENTORY MARKS BOTH "NOT SUPPLIED, and not suppliable today"
--   (lj-1.570-report.md:48, :78).
--
--   THIS SECTION CUTS THE TWO STATEMENTS DOWN TO THREE FACTS, AND
--   NEITHER FACT MENTIONS THE COLLAPSE'S CARRIER `πX`.  That is the
--   point: `LevelInH` and `CoverH` both quantify over `HS.C.πX`, and
--   `πX` is only known to be a stage AFTER `Condense` runs, which is
--   what consumes them.  The three facts below quantify over the HULL
--   `HS.M` and over `HS.C.π` pointwise, so they can be attacked without
--   that circularity.
--
--   The collapse machinery that carries them across is DELIVERED:
--   `πX-member`, `πX-intro` and `π∈-fwd` (src/V/Collapse.lagda.md:78,
--   :86, :102).  Nothing in this section is new mathematics; it is a
--   re-factoring, and its whole content is the line count in section 8.
-- =====================================================================

module Facts (lam : SV.S) (ordλ : IsOrd lam)
             (succλ : (d : SV.S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
             (X : SV.S)
             (X⊆Lλ : (z : SV.S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
             (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  module HS = HullStage lam ordλ succλ X X⊆Lλ ∅∈λ
  module A570 = P570.AtHull lam ordλ succλ X X⊆Lλ ∅∈λ

  -- FACT A.  The hull is closed under the level construction, at those
  -- of its members the collapse sends to an ordinal.
  HasLevels : Type (ℓ-suc ℓ)
  HasLevels = (δ : SV.S) → ⟨ δ ∈ˢ HS.M ⟩ → IsOrd (HS.C.π δ)
            → ⟨ Lset δ ∈ˢ HS.M ⟩

  -- FACT B.  The collapse commutes with the level construction there.
  -- THIS IS THE CONDENSATION'S CORE and section 5 names its price.
  LevelsCommute : Type (ℓ-suc ℓ)
  LevelsCommute = (δ : SV.S) → ⟨ δ ∈ˢ HS.M ⟩ → IsOrd (HS.C.π δ)
                → HS.C.π (Lset δ) ≡ Lset (HS.C.π δ)

  -- FACT C.  Every hull member sits inside a level indexed IN THE HULL.
  Covered : Type (ℓ-suc ℓ)
  Covered = (y : SV.S) → ⟨ y ∈ˢ HS.M ⟩
          → ∥ Σ[ γ ∈ SV.S ]
               ( ⟨ γ ∈ˢ HS.M ⟩
               × IsOrd (HS.C.π γ)
               × ⟨ y ∈ˢ Lset γ ⟩ ) ∥₁

  -- `levelIn` NEEDS A AND B, AND NOTHING ELSE.
  levelIn-from : HasLevels → LevelsCommute → A570.LevelInH
  levelIn-from hl lc δ oδ δ∈πX =
    PT.rec (snd (Lset δ ∈ˢ HS.C.πX)) go (HS.C.πX-member δ δ∈πX)
    where
    go : Σ[ γ ∈ SV.S ] (⟨ γ ∈ˢ HS.M ⟩ × (HS.C.π γ ≡ δ))
       → ⟨ Lset δ ∈ˢ HS.C.πX ⟩
    go (γ , γ∈M , e) =
      subst (λ w → ⟨ w ∈ˢ HS.C.πX ⟩) (lc γ γ∈M oγ ∙ cong Lset e)
        (HS.C.πX-intro (Lset γ) (hl γ γ∈M oγ))
      where
      oγ : IsOrd (HS.C.π γ)
      oγ = subst IsOrd (sym e) oδ

  -- `cover` NEEDS B AND C, AND NOT A.
  cover-from : LevelsCommute → Covered → A570.CoverH
  cover-from lc cv y y∈M = PT.map go (cv y y∈M)
    where
    go : Σ[ γ ∈ SV.S ]
           (⟨ γ ∈ˢ HS.M ⟩ × IsOrd (HS.C.π γ) × ⟨ y ∈ˢ Lset γ ⟩)
       → Σ[ γ ∈ SV.S ]
           ( IsOrd γ
           × ⟨ γ ∈ˢ HS.C.πX ⟩
           × ⟨ HS.C.π y ∈ˢ Lset γ ⟩ )
    go (γ , γ∈M , oπγ , y∈Lγ) =
        HS.C.π γ
      , oπγ
      , HS.C.πX-intro γ γ∈M
      , subst (λ w → ⟨ HS.C.π y ∈ˢ w ⟩) (lc γ γ∈M oπγ)
          (HS.C.π∈-fwd (Lset γ) y y∈Lγ y∈M)

-- THE THREE FACTS, AT EVERY HULL.  This is [LJ-1.570]'s
-- `HullCondensation` (Probe570.agda:168-176) with its two statements
-- replaced by these three.
ThreeFacts : Type (ℓ-suc ℓ)
ThreeFacts =
    (lam : SV.S) (ordλ : IsOrd lam)
    (succλ : (d : SV.S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
    (X : SV.S)
    (X⊆Lλ : (z : SV.S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
    (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩)
  → Facts.HasLevels     lam ordλ succλ X X⊆Lλ ∅∈λ
  × Facts.LevelsCommute lam ordλ succλ X X⊆Lλ ∅∈λ
  × Facts.Covered       lam ordλ succλ X X⊆Lλ ∅∈λ

three-give-hull : ThreeFacts → P570.HullCondensation
three-give-hull tf lam ordλ succλ X X⊆Lλ ∅∈λ =
    F.levelIn-from (tf lam ordλ succλ X X⊆Lλ ∅∈λ .fst)
                   (tf lam ordλ succλ X X⊆Lλ ∅∈λ .snd .fst)
  , F.cover-from   (tf lam ordλ succλ X X⊆Lλ ∅∈λ .snd .fst)
                   (tf lam ordλ succλ X X⊆Lλ ∅∈λ .snd .snd)
  where
  module F = Facts lam ordλ succλ X X⊆Lλ ∅∈λ

-- AND THE THREE FACTS GIVE `CoHyps` AT THE FRAME `gch-from-five` CALLS
-- IT, through [LJ-1.570]'s own reduction and nothing else.
three-give-cohyps : ThreeFacts → P550.CoHyps
three-give-cohyps tf = P570.cohyps-at-today (three-give-hull tf)

-- AND THE WHOLE BILL, with row 3 replaced by the three facts.
gch-from-three : (zf : ModelL.isZFModel)
  → P550.AmbientCardAtSucc → P550.SqAt → ThreeFacts
  → P564.StageCountedCoded → P558.SuccIntoPower zf
  → GCHStatement zf
gch-from-three zf r1 r2 tf b9 b10 =
  P564.gch-from-five zf r1 r2 (three-give-cohyps tf) b9 b10

-- =====================================================================
-- SECTION 3.  THE ATTEMPT.  WHAT DISCHARGES FACT A AND FACT C.
--
--   Facts A and C are the SAME shape and the shape is the hull's own
--   Skolem closure, `src/L/Hull.lagda.md:120`.  `closed` takes a
--   formula over hull codes that the stage's inner world satisfies, and
--   returns a witness INSIDE the hull.  So each of A and C is one
--   formula away, and this section pays everything except the formula.
--
--   WHAT IS LEFT AFTER THIS SECTION IS THE LEVEL-HOOD CERTIFICATE, AND
--   THE BRIEF FORBIDS ME TO BUILD IT.  It is named here as a TYPE, not
--   as prose, so the next brief reads it at `file:line`.
-- =====================================================================

open import FOL.Syntax using ( Formula )

module Cert (lam : SV.S) (ordλ : IsOrd lam)
            (succλ : (d : SV.S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
            (X : SV.S)
            (X⊆Lλ : (z : SV.S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
            (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  module HS = HullStage lam ordλ succλ X X⊆Lλ ∅∈λ
  module F = Facts lam ordλ succλ X X⊆Lλ ∅∈λ
  module T = HS.H.T

  -- CLAUSE (i).  The level at an ordinal of the hull is DEFINED, in the
  -- stage's inner world, by a formula over hull constants.  This is the
  -- level-hood certificate at the hull, and nothing else.
  DefinesLevel : Type (ℓ-suc ℓ)
  DefinesLevel =
    (c : T.Code) → IsOrd (HS.C.π (fst (T.val c)))
    → Σ[ φ ∈ Formula T.Code 1 ]
        ( ∥ Σ[ a ∈ HS.ASt.SL ] ⟨ (a ∷ []) T.⊨c φ ⟩ ∥₁
        × ((a : HS.ASt.SL) → ⟨ (a ∷ []) T.⊨c φ ⟩
           → fst a ≡ Lset (fst (T.val c))) )

  -- CLAUSE (ii).  The covering ordinal of a hull member is DEFINED the
  -- same way.  Its witness need not be unique: any witness serves.
  DefinesCover : Type (ℓ-suc ℓ)
  DefinesCover =
    (c : T.Code)
    → Σ[ φ ∈ Formula T.Code 1 ]
        ( ∥ Σ[ a ∈ HS.ASt.SL ] ⟨ (a ∷ []) T.⊨c φ ⟩ ∥₁
        × ((a : HS.ASt.SL) → ⟨ (a ∷ []) T.⊨c φ ⟩
           → IsOrd (HS.C.π (fst a))
           × ⟨ fst (T.val c) ∈ˢ Lset (fst a) ⟩) )

  -- FACT A IS PAID FROM CLAUSE (i).
  cert-gives-A : DefinesLevel → F.HasLevels
  cert-gives-A dl δ δ∈M oπδ =
    PT.rec (snd (Lset δ ∈ˢ HS.M)) go (HS.H.hull-member δ δ∈M)
    where
    go : Σ[ c ∈ T.Code ] (fst (T.val c) ≡ δ) → ⟨ Lset δ ∈ˢ HS.M ⟩
    go (c , e) = PT.rec (snd (Lset δ ∈ˢ HS.M)) go₂ (T.closed φ sat)
      where
      oc : IsOrd (HS.C.π (fst (T.val c)))
      oc = subst (λ w → IsOrd (HS.C.π w)) (sym e) oπδ
      φ : Formula T.Code 1
      φ = fst (dl c oc)
      sat : ∥ Σ[ a ∈ HS.ASt.SL ] ⟨ (a ∷ []) T.⊨c φ ⟩ ∥₁
      sat = fst (snd (dl c oc))
      go₂ : Σ[ a ∈ HS.ASt.SL ]
              (⟨ fst a ∈ˢ T.Hull ⟩ × ⟨ (a ∷ []) T.⊨c φ ⟩)
          → ⟨ Lset δ ∈ˢ HS.M ⟩
      go₂ (a , a∈M , ha) =
        subst (λ w → ⟨ w ∈ˢ HS.M ⟩)
          (snd (snd (dl c oc)) a ha ∙ cong Lset e) a∈M

  -- FACT C IS PAID FROM CLAUSE (ii).
  cert-gives-C : DefinesCover → F.Covered
  cert-gives-C dc y y∈M =
    PT.rec PT.squash₁ go (HS.H.hull-member y y∈M)
    where
    go : Σ[ c ∈ T.Code ] (fst (T.val c) ≡ y)
       → ∥ Σ[ γ ∈ SV.S ]
             (⟨ γ ∈ˢ HS.M ⟩ × IsOrd (HS.C.π γ) × ⟨ y ∈ˢ Lset γ ⟩) ∥₁
    go (c , e) = PT.map go₂ (T.closed φ sat)
      where
      φ : Formula T.Code 1
      φ = fst (dc c)
      sat : ∥ Σ[ a ∈ HS.ASt.SL ] ⟨ (a ∷ []) T.⊨c φ ⟩ ∥₁
      sat = fst (snd (dc c))
      go₂ : Σ[ a ∈ HS.ASt.SL ]
              (⟨ fst a ∈ˢ T.Hull ⟩ × ⟨ (a ∷ []) T.⊨c φ ⟩)
          → Σ[ γ ∈ SV.S ]
              (⟨ γ ∈ˢ HS.M ⟩ × IsOrd (HS.C.π γ) × ⟨ y ∈ˢ Lset γ ⟩)
      go₂ (a , a∈M , ha) =
          fst a
        , a∈M
        , fst (snd (snd (dc c)) a ha)
        , subst (λ w → ⟨ w ∈ˢ Lset (fst a) ⟩) e
            (snd (snd (snd (dc c)) a ha))

-- =====================================================================
-- SECTION 4.  ONE LEG OF THE REMAINDER, PAID.  THE COLLAPSE'S
-- SATISFACTION TRANSFER, AS A TERM AT THIS SITE.
--
--   [LJ-1.570] listed the collapse iso among the pieces that have
--   "their machinery in src/ and no term at the site"
--   (lj-1.570-report.md:60-63, naming src/L/BoundedSubset.lagda.md:152
--   and :321).  THE MACHINERY IS `IsoInv` (:152) AND IT IS COMPLETE:
--   `iso-inv` (:195) transfers satisfaction of EVERY formula across
--   the collapse, and `CollapseIso` (:321) already instantiates it
--   (:350).  What was missing is the instance at the HULL's collapse,
--   and `HullExt.hullExt` (:1340) is the extensionality it wants.
--
--   THE TERM IS BELOW.  It is the middle leg of Fact B's chain, and it
--   is now free.
-- =====================================================================

open import FOL.Manipulation.Relabelling using ( mapFo )
open import L.BoundedSubset {ℓ} lem using ( module HullExt; module CollapseIso )

module AtCollapse (lam : SV.S) (ordλ : IsOrd lam)
                  (succλ : (d : SV.S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
                  (X : SV.S)
                  (X⊆Lλ : (z : SV.S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
                  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  module HS = HullStage lam ordλ succλ X X⊆Lλ ∅∈λ
  module HE = HullExt lam ordλ X X⊆Lλ ∅∈λ
  module CIso = CollapseIso HS.M HE.hullExt

  -- The transfer, at one free variable, which is the arity Fact B needs.
  iso-inv-at-the-site : (φ : Formula CIso.I.SM 1) (q : CIso.I.SM)
                      → ⟨ (q ∷ []) CIso.I.⊨ᵐ φ ⟩
                      → ⟨ (CIso.I.g q ∷ []) CIso.I.⊨ᵖᵐ mapFo CIso.I.g φ ⟩
  iso-inv-at-the-site φ q = CIso.I.iso-inv 1 φ (q ∷ [])

  -- And the collapse of the site IS the collapse the pair speaks about.
  same-collapse : CIso.PM ≡ HS.C.πX
  same-collapse = refl

-- =====================================================================
-- SECTION 5.  THE REFLECTION STEP OF [LJ-1.560], TRIED AGAINST THE PAIR.
--
--   MEASURED FIRST: [LJ-1.570] DID NOT TRY IT.  Its brief is not in the
--   tree (`ls agents/tasks/LJ-1-570/` returns four entries and none is
--   `LJ-1.570.md`, though review-of-cohyps.md:7 cites it), so I cannot
--   check what it was TOLD.  What it DID is checkable:
--   `grep -rn "560\|search-bounds\|reflect" agents/tasks/LJ-1-570/`
--   returns EIGHT hits.  SIX are the string "down-reflection", which is
--   `DR54.ElemDown` and a different thing (Probe570.agda:136;
--   lj-1.570-report.md:39, :59, :174; review-of-cohyps.md:28, :46).
--   The other two match on digits alone: lj-1.570-report.md:70 inside
--   the reference ":1560", and runs/s1-2.out:24 inside an instruction
--   count.  THE STRICT GREP RETURNS ZERO:
--   `grep -rn "LJ-1\.560\|LJ-1-560\|search-bounds\|mkReflect\|Single\.reflect"
--   agents/tasks/LJ-1-570/`.
--
--   AND IT DOES NOT APPLY, FOR A REASON THAT IS A TYPE AND NOT AN
--   OPINION.  `search-bounds` (Probe560.agda:165-176) takes a FORMULA
--   and returns a STAGE at which its unbounded existential is answered.
--   `levelIn` and `cover` do not quantify over a stage: they quantify
--   over `HS.C.πX`, the collapse's carrier.  The one thing in the tree
--   that identifies that carrier with a stage is `Condense.condenses`
--   (src/L/BoundedSubset.lagda.md:1033), AND IT CONSUMES THE PAIR.
--   The term below is that consumption, so the circle is closed in
--   Agda and not in prose.
-- =====================================================================

module Circle (lam : SV.S) (ordλ : IsOrd lam)
              (succλ : (d : SV.S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
              (X : SV.S)
              (X⊆Lλ : (z : SV.S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
              (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  module HS = HullStage lam ordλ succλ X X⊆Lλ ∅∈λ
  module A570 = P570.AtHull lam ordλ succλ X X⊆Lλ ∅∈λ

  -- THE PAIR GIVES THE STAGE.  Delivered, and this is the direction
  -- that already runs.
  pair-gives-stage : A570.LevelInH → A570.CoverH
                   → Σ[ β ∈ SV.S ] (IsOrd β × (HS.C.πX ≡ Lset β))
  pair-gives-stage li cv = HS.Condense.condenses li cv

  -- THE OTHER DIRECTION IS WHAT A REFLECTION PRINCIPLE WOULD HAVE TO
  -- SUPPLY, and it is not stated anywhere in the tree.  I did not
  -- inhabit it and I do not claim it is true at this frame; it is
  -- written as a TYPE so the next brief can price it.
  StageGivesPair : Type (ℓ-suc ℓ)
  StageGivesPair =
      (β : SV.S) → IsOrd β → (HS.C.πX ≡ Lset β)
    → A570.LevelInH × A570.CoverH

-- =====================================================================
-- SECTION 6.  WHAT I TOOK FROM [LJ-1.570], BY USE AND NOT BY QUOTATION.
--
--   The brief ordered its 41 measured lines RE-USED and not rebuilt.
--   `Probe570.agda:251-337` is imported, not copied, and the two terms
--   below are the whole of it, ascribed here so that a failure in that
--   file would be a failure in this one.  Section 8 of the report says
--   which lines I took.
-- =====================================================================

module SL = hPropStructure 𝒮ʟ

-- [LJ-1.304]'s "last unpriced term", live at today's tree, TAKEN.
levels-decode :
    P570.GraphAgree → (m : SL.S) → IsOrd (fst m) → P570.Adeq m
  → ∥ Σ[ K' ∈ SL.S ] Σ[ v' ∈ SL.S ]
      (⟨ v' SL.∈ˢ K' ⟩ × (fst v' ≡ Lset (fst m))) ∥₁
levels-decode = P570.adeq-decode

-- And the down-reflection [LJ-1.52] listed as owed, also TAKEN.  It
-- lives at the SEVENTEEN-slot frame and not at the six
-- (lj-1.570-report.md:37-42), so a supplier that wants it must widen.
elem-down-taken :
    (κ : SV.S) (ordκ : IsOrd κ) (cardκ : IsCardinal κ)
    (κ∉ω : ⟨ κ ∈ˢ ω ⟩ → Empty.⊥)
    (α : SV.S) (ordα : IsOrd α) (α∈κ : ⟨ α ∈ˢ κ ⟩)
    (α∉ω : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
    (sq : P550.SqLaw α)
    (x : SV.S) (x⊆Lα : (z : SV.S) → ⟨ z ∈ˢ x ⟩ → ⟨ z ∈ˢ Lset α ⟩)
    (absorbs : ⟪ Lset α ∪ ⁅ x ⁆s ⟫ ↪ ⟪ Lset α ⟫)
    (lam : SV.S) (ordλ : IsOrd lam) (α∈λ : ⟨ α ∈ˢ lam ⟩)
    (succλ : (d : SV.S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
    (x∈Lλ : ⟨ x ∈ˢ Lset lam ⟩)
  → P550.Tele.BSA.DR54.ElemDown
      κ ordκ cardκ κ∉ω α ordα α∈κ α∉ω sq x x⊆Lα absorbs
      lam ordλ α∈λ succλ x∈Lλ
elem-down-taken = P570.elem-down-at-the-site

-- =====================================================================
-- SECTION 7.  THE REMAINDER, NAMED AS ONE TYPE.
--
--   THIS IS THE NO-GO DELIVERABLE.  `CoHyps` is not supplied.  What it
--   is short of is exactly the three statements below, and the term
--   after them is the proof that nothing else is short.
--
--   Clause (i) and clause (ii) are the LEVEL-HOOD CERTIFICATE at the
--   hull, which the brief forbids me to build and which I have not
--   built.  `LevelsCommute` is the collapse-side half of the same
--   formula, and section 4 pays its middle leg.
-- =====================================================================

Remainder : Type (ℓ-suc ℓ)
Remainder =
    (lam : SV.S) (ordλ : IsOrd lam)
    (succλ : (d : SV.S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
    (X : SV.S)
    (X⊆Lλ : (z : SV.S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
    (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩)
  → Cert.DefinesLevel  lam ordλ succλ X X⊆Lλ ∅∈λ
  × Cert.DefinesCover  lam ordλ succλ X X⊆Lλ ∅∈λ
  × Facts.LevelsCommute lam ordλ succλ X X⊆Lλ ∅∈λ

remainder-gives-three : Remainder → ThreeFacts
remainder-gives-three r lam ordλ succλ X X⊆Lλ ∅∈λ =
    C.cert-gives-A (r lam ordλ succλ X X⊆Lλ ∅∈λ .fst)
  , r lam ordλ succλ X X⊆Lλ ∅∈λ .snd .snd
  , C.cert-gives-C (r lam ordλ succλ X X⊆Lλ ∅∈λ .snd .fst)
  where
  module C = Cert lam ordλ succλ X X⊆Lλ ∅∈λ

-- THE WHOLE OF ROW 3, ABOVE THE REMAINDER.
remainder-gives-cohyps : Remainder → P550.CoHyps
remainder-gives-cohyps r = three-give-cohyps (remainder-gives-three r)

-- AND THE WHOLE BILL, above the remainder and nothing else.
gch-above-the-remainder : (zf : ModelL.isZFModel)
  → P550.AmbientCardAtSucc → P550.SqAt → Remainder
  → P564.StageCountedCoded → P558.SuccIntoPower zf
  → GCHStatement zf
gch-above-the-remainder zf r1 r2 r b9 b10 =
  P564.gch-from-five zf r1 r2 (remainder-gives-cohyps r) b9 b10

-- =====================================================================
-- SECTION 8.  FACT B, REDUCED TO THE SAME CERTIFICATE, READ IN THE
-- COLLAPSE.
--
--   Section 7 left `LevelsCommute` standing as a statement of its own.
--   It is not one.  It is the SAME formula read a third time, and this
--   section pays everything between the readings, using section 4's
--   term for the middle leg.
--
--   AFTER THIS SECTION THE REMAINDER IS ONE OBJECT: a formula that
--   defines the level construction, together with the fact that it does
--   so at the STAGE (clause i), for the COVER (clause ii) and in the
--   COLLAPSE (clause iii).  That object is the level-hood certificate.
--   THE BRIEF FORBIDS ME TO BUILD IT AND I HAVE NOT BUILT IT.
-- =====================================================================

module BChain (lam : SV.S) (ordλ : IsOrd lam)
              (succλ : (d : SV.S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
              (X : SV.S)
              (X⊆Lλ : (z : SV.S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
              (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  module HS = HullStage lam ordλ succλ X X⊆Lλ ∅∈λ
  module F  = Facts     lam ordλ succλ X X⊆Lλ ∅∈λ
  module AC = AtCollapse lam ordλ succλ X X⊆Lλ ∅∈λ
  module CI = AC.CIso

  -- CLAUSE (iii).  The level at an ordinal of the hull is defined, in
  -- the HULL's inner world, by a formula whose reading in the COLLAPSE
  -- pins the true level there.
  DefinesLevelAcross : Type (ℓ-suc ℓ)
  DefinesLevelAcross =
    (δ : SV.S) (δ∈M : ⟨ δ ∈ˢ HS.M ⟩) → IsOrd (HS.C.π δ)
    → (Lδ∈M : ⟨ Lset δ ∈ˢ HS.M ⟩)
    → Σ[ φ ∈ Formula CI.I.SM 1 ]
        ( ⟨ ((Lset δ , Lδ∈M) ∷ []) CI.I.⊨ᵐ φ ⟩
        × ((b : CI.I.SPM) → ⟨ (b ∷ []) CI.I.⊨ᵖᵐ mapFo CI.I.g φ ⟩
           → fst b ≡ Lset (HS.C.π δ)) )

  -- FACT B IS PAID FROM CLAUSE (iii) AND FACT A.
  b-from-across : F.HasLevels → DefinesLevelAcross → F.LevelsCommute
  b-from-across hl da δ δ∈M oπδ =
    snd (snd (da δ δ∈M oπδ Lδ∈M))
      (CI.I.g (Lset δ , Lδ∈M))
      (AC.iso-inv-at-the-site (fst (da δ δ∈M oπδ Lδ∈M))
        (Lset δ , Lδ∈M)
        (fst (snd (da δ δ∈M oπδ Lδ∈M))))
    where
    Lδ∈M : ⟨ Lset δ ∈ˢ HS.M ⟩
    Lδ∈M = hl δ δ∈M oπδ

-- THE CERTIFICATE, IN ITS THREE READINGS AND NOTHING ELSE.
Certificate : Type (ℓ-suc ℓ)
Certificate =
    (lam : SV.S) (ordλ : IsOrd lam)
    (succλ : (d : SV.S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
    (X : SV.S)
    (X⊆Lλ : (z : SV.S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
    (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩)
  → Cert.DefinesLevel          lam ordλ succλ X X⊆Lλ ∅∈λ
  × Cert.DefinesCover          lam ordλ succλ X X⊆Lλ ∅∈λ
  × BChain.DefinesLevelAcross  lam ordλ succλ X X⊆Lλ ∅∈λ

certificate-gives-remainder : Certificate → Remainder
certificate-gives-remainder c lam ordλ succλ X X⊆Lλ ∅∈λ =
    c lam ordλ succλ X X⊆Lλ ∅∈λ .fst
  , c lam ordλ succλ X X⊆Lλ ∅∈λ .snd .fst
  , B.b-from-across (C.cert-gives-A (c lam ordλ succλ X X⊆Lλ ∅∈λ .fst))
                    (c lam ordλ succλ X X⊆Lλ ∅∈λ .snd .snd)
  where
  module C = Cert   lam ordλ succλ X X⊆Lλ ∅∈λ
  module B = BChain lam ordλ succλ X X⊆Lλ ∅∈λ

-- AND THE WHOLE OF ROW 3 FROM THE CERTIFICATE ALONE.
certificate-gives-cohyps : Certificate → P550.CoHyps
certificate-gives-cohyps c =
  remainder-gives-cohyps (certificate-gives-remainder c)

-- THE BILL, above ONE object.
gch-above-the-certificate : (zf : ModelL.isZFModel)
  → P550.AmbientCardAtSucc → P550.SqAt → Certificate
  → P564.StageCountedCoded → P558.SuccIntoPower zf
  → GCHStatement zf
gch-above-the-certificate zf r1 r2 c b9 b10 =
  P564.gch-from-five zf r1 r2 (certificate-gives-cohyps c) b9 b10

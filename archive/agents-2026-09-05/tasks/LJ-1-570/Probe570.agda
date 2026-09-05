{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.570]  `levelIn` and `cover`, re-priced at today's tree.
--
-- W3 IS SECTION 1 and the brief ordered it written FIRST and typechecked
-- ALONE.  The slice is agents/tasks/LJ-1-570/runs/W3.agda; its runs are
-- runs/w3-1.out (exit 42, a missing import) and runs/w3-2.out (exit 0).
--
-- Nothing is postulated.  Nothing lands in src/.  No hole.
--
-- CALIBER.  The program set GHCRTS="-A64m -I0 -M8g" on this pane.  I did
-- not set it.  One Agda process at a time.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-570.Probe570 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; IsOrd; Lset; isL; isL-trans )
open import L.GCH {ℓ} lem using ( GCHStatement )
open import FOL.Syntax using ( Formula; var; _≐_; _∧̇_ )
open import L.Coding.Sequence {ℓ} lem using ( LsetGraphAt )
open import L.Condensation {ℓ} lem using ( ride-only )
import FOL.Absoluteness
import FOL.ZFModel
open import Cubical.HITs.CumulativeHierarchy.Base using ( setIsSet )
open import L.Ordinal {ℓ} using ( suc-ord )
open import L.BoundedSubset {ℓ} lem
  using ( IsCardinal; _↪_; module Devlin55; module HullStage
        ; module DownReflect; module LevelHood0 )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; _∪_; ⁅_⁆s; ∅ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open InfinitySet {ℓ} using ( ω; sucV )
open import Cubical.Data.Sigma using ( _×_ )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

-- THE PREDECESSORS, BY THE TYPE EACH ONE DELIVERED.
-- [LJ-1.550] is NO-GO on its own obligation only
-- (agents/tasks/LJ-1-550/lj-1.550-report.md:16); the module is green and
-- `CoHyps` is a TYPE in it, so taking the type is taking what that task
-- delivered.  [LJ-1.564] is GO (lj-1.564-report.md:3).
import LJ-1-550.Probe550 {ℓ} lem as P550
import LJ-1-558.Probe558 {ℓ} lem as P558
import LJ-1-564.Probe564 {ℓ} lem as P564

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
module SV = hPropStructure 𝒮ᵥ
module SL = hPropStructure 𝒮ʟ
module ModelL = FOL.ZFModel 𝒮ʟ
module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open SV using ( _∈ˢ_ )

-- =====================================================================
-- SECTION 1.  W3.  THE WIDEST UNMEASURED TERM, TYPE ONLY.
--
--   `levelIn` alone, re-ascribed at the frame `gch-from-five` calls it.
--   `CoHyps` (Probe550.agda:215-230) is a PAIR; this is its first
--   component over the same seventeen-slot telescope.  No inhabitant.
-- =====================================================================

LevelInAt : Type (ℓ-suc ℓ)
LevelInAt =
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
  → P550.Tele.LevelIn κ ordκ cardκ κ∉ω α ordα α∈κ α∉ω sq x x⊆Lα absorbs
      lam ordλ α∈λ succλ x∈Lλ

-- The `cover` half, at the same telescope.  Together they are `CoHyps`.
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

-- The two halves ARE `CoHyps`, and the elaborator says so.
halves-are-cohyps : LevelInAt → CoverAt → P550.CoHyps
halves-are-cohyps li cv κ ordκ cardκ κ∉ω α ordα α∈κ α∉ω sq x x⊆Lα absorbs
                  lam ordλ α∈λ succλ x∈Lλ =
    li κ ordκ cardκ κ∉ω α ordα α∈κ α∉ω sq x x⊆Lα absorbs
       lam ordλ α∈λ succλ x∈Lλ
  , cv κ ordκ cardκ κ∉ω α ordα α∈κ α∉ω sq x x⊆Lα absorbs
       lam ordλ α∈λ succλ x∈Lλ

-- And `CoHyps` is row 3 of the campaign's five, by [LJ-1.564]'s own
-- term and not by quotation (Probe564.agda:456-463).
row3-is-cohyps :
    (zf : ModelL.isZFModel)
  → P550.AmbientCardAtSucc → P550.SqAt → P550.CoHyps
  → P564.StageCountedCoded
  → P558.SuccIntoPower zf
  → GCHStatement zf
row3-is-cohyps = P564.gch-from-five

-- =====================================================================
-- SECTION 2.  D-10, AND IT IS THE INVENTORY'S FIRST ANSWER.
--
--   ELEVEN OF THE SEVENTEEN SLOTS ARE DEAD WEIGHT.  `CoHyps` is stated
--   over the bounded subset theorem's whole telescope, and the archive
--   has priced it there for four hundred dispatches.  But `LevelIn` and
--   `Cover` name only `BSA.HS.C.πX`, `BSA.HS.M` and `BSA.HS.C.π`
--   (Probe550.agda:104-113), and `BSA.HS` is
--   `HullStage lam ordλ succλ UK.X UK.X⊆Lλ UK.∅∈λ`
--   (src/L/BoundedSubset.lagda.md:1405).  So the two hypotheses live at
--   SIX slots and not seventeen.
--
--   The cardinal, the square law, the subset, the absorption, the two
--   omega side conditions, `α`, `α∈κ`, `α∈λ`, `κ` and `x` reach them
--   ONLY through `UK.X`, and a supplier that is total in `X` never sees
--   any of them.
--
--   THIS IS A SUFFICIENT CONDITION AND NOT AN EQUIVALENT ONE, and the
--   report says so.  Section 4 shows the tree's own down-reflection
--   lives at the SEVENTEEN-slot frame, because its code selection needs
--   `α`'s well-order and the hull's code count
--   (src/L/BoundedSubset.lagda.md:1515-1545).  So a supplier that wants
--   `elem-down` must take the wider frame; a supplier that does not,
--   need not.
-- =====================================================================

module AtHull (lam : SV.S) (ordλ : IsOrd lam)
              (succλ : (d : SV.S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
              (X : SV.S)
              (X⊆Lλ : (z : SV.S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
              (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  module HS = HullStage lam ordλ succλ X X⊆Lλ ∅∈λ

  -- `Co`'s first parameter, at the hull and nothing else
  -- (src/L/BoundedSubset.lagda.md:1555-1556).
  LevelInH : Type (ℓ-suc ℓ)
  LevelInH = (δ : SV.S) → IsOrd δ → ⟨ δ ∈ˢ HS.C.πX ⟩ → ⟨ Lset δ ∈ˢ HS.C.πX ⟩

  -- `Co`'s second parameter (:1557-1558).
  CoverH : Type (ℓ-suc ℓ)
  CoverH = (y : SV.S) → ⟨ y ∈ˢ HS.M ⟩
         → ∥ Σ[ γ ∈ SV.S ]
              ( IsOrd γ
              × ⟨ γ ∈ˢ HS.C.πX ⟩
              × ⟨ HS.C.π y ∈ˢ Lset γ ⟩ ) ∥₁

-- THE SIX-SLOT STATEMENT.  Condensation at every hull over every
-- carrier inside every limit stage.  Nothing about cardinals, nothing
-- about the square law, nothing about the subset being bounded.
HullCondensation : Type (ℓ-suc ℓ)
HullCondensation =
    (lam : SV.S) (ordλ : IsOrd lam)
    (succλ : (d : SV.S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
    (X : SV.S)
    (X⊆Lλ : (z : SV.S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
    (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩)
  → AtHull.LevelInH lam ordλ succλ X X⊆Lλ ∅∈λ
  × AtHull.CoverH  lam ordλ succλ X X⊆Lλ ∅∈λ

-- =====================================================================
-- SECTION 3.  THE OBLIGATION.
--
--   The brief allows the obligation to be "the term that names
--   precisely what is missing".  This is it: `CoHyps` at the frame
--   `gch-from-five` calls it, from the SIX-slot statement and nothing
--   else.  The eleven other slots are discharged by the elaborator, not
--   by an argument in prose.
-- =====================================================================

cohyps-at-today : HullCondensation → P550.CoHyps
cohyps-at-today h κ ordκ cardκ κ∉ω α ordα α∈κ α∉ω sq x x⊆Lα absorbs
                lam ordλ α∈λ succλ x∈Lλ =
  h lam ordλ succλ T.BSA.UK.X T.BSA.UK.X⊆Lλ T.BSA.UK.∅∈λ
  where
  module T = P550.Tele κ ordκ cardκ κ∉ω α ordα α∈κ α∉ω sq x x⊆Lα absorbs
                       lam ordλ α∈λ succλ x∈Lλ

-- AND THE BILL, WITH ROW 3 REPLACED BY THE SIX-SLOT STATEMENT.
-- Read the hypothesis list: `CoHyps` is gone and `HullCondensation`
-- stands in its place, at the same target.
gch-from-five-at-the-hull :
    (zf : ModelL.isZFModel)
  → P550.AmbientCardAtSucc → P550.SqAt → HullCondensation
  → P564.StageCountedCoded
  → P558.SuccIntoPower zf
  → GCHStatement zf
gch-from-five-at-the-hull zf r1 r2 hc b9 b10 =
  P564.gch-from-five zf r1 r2 (cohyps-at-today hc) b9 b10

-- =====================================================================
-- SECTION 4.  WHAT THE TREE DELIVERS TOWARD THE SIX-SLOT STATEMENT.
--
--   [LJ-1.52] named SIX survivors, three per hypothesis
--   (agents/tasks/archive/LJ-1-52/lj-1.52-report.md:17-18).  ONE of the
--   six is a TERM at the site today, and it is the one this section
--   ascribes.  Two more have their machinery in src/ and no term at the
--   site: the hull's Skolem closure (src/L/Hull.lagda.md:120) and the
--   collapse iso (src/L/BoundedSubset.lagda.md:152, :321).  The other
--   three are not built anywhere.
-- =====================================================================

-- 4.1  THE DOWN-REFLECTION.  [LJ-1.52] listed it as OWED for `levelIn`,
-- and asked for it at ARITY ONE
-- (agents/tasks/archive/LJ-1-52/lj-1.52-report.md:17).  It is
-- DELIVERED today, at src/L/BoundedSubset.lagda.md:1547-1548, INSIDE the
-- module `Co` sits in.  `DR54` is the tree's own name for its type
-- (:1549), so this ascription names no transparent construction.
--
-- P-l, MEASURED HERE AND NOT INHERITED.  The first spelling of this same
-- fact put `Tele.BSA.UK.X`, `.X⊆Lλ` and `.∅∈λ` INTO the type, at the
-- generic telescope.  That spelling ran 443.62 s at a flat 1.89 GB and
-- did not finish; I stopped it (runs/s4-2.out, EXIT=143, and the flat
-- resident set says it was NOT a heap event).  The opaque spelling below
-- is the same fact.
elem-down-at-the-site :
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
elem-down-at-the-site κ ordκ cardκ κ∉ω α ordα α∈κ α∉ω sq x x⊆Lα absorbs
                      lam ordλ α∈λ succλ x∈Lλ =
  P550.Tele.BSA.elem-down κ ordκ cardκ κ∉ω α ordα α∈κ α∉ω sq x x⊆Lα absorbs
                          lam ordλ α∈λ succλ x∈Lλ

-- =====================================================================
-- SECTION 5.  THE ARCHIVED ASSEMBLY, RE-LANDED AT TODAY'S TREE.
--
--   [LJ-1.304] section 10 named this "the last unpriced term on q's
--   route" and INFERRED it at about 40 lines
--   (agents/tasks/LJ-1-304/lj-1.304-report.md:333-340).  It is
--   [LJ-1.52]'s `matrix-decode` and `adeq-decode`
--   (agents/tasks/archive/LJ-1-52/ProbeLJ152A.agda:58-96), which have
--   never been re-run against the tree as it stands.  This section is
--   that port, and its line count is the price the brief asked for.
--
--   `LevelHood0` still exists, at src/L/BoundedSubset.lagda.md:840-869,
--   and `ride-only` still exists, at src/L/Condensation.lagda.md:422.
--   Nothing here is new mathematics: it is a MEASUREMENT that the
--   archived shape still typechecks four hundred dispatches later.
-- =====================================================================

module LH0 = LevelHood0
  zero zero zero zero zero zero zero zero zero zero zero zero zero zero
  zero zero zero zero zero zero zero zero zero zero zero zero zero zero

-- THE PORT IS NOT A COPY, AND THAT IS THIS SECTION'S FIRST
-- MEASUREMENT.  [LJ-1.52] read the value at slot 1 of the inner env
-- and wrote `LsetGraphAt (suc zero) (suc (suc (suc zero)))`
-- (ProbeLJ152A.agda:52-54).  TODAY `LevelHood` instantiates `GraphB` at
-- `zero (suc (suc (suc zero))) (suc (suc (suc (suc zero))))`
-- (src/L/BoundedSubset.lagda.md:104), so the graph's VALUE slot is 0,
-- slot 0 of the outer environment is unused (:69-71), and the value is
-- slot 1, reached only through the `≐` conjunct.  **The archived
-- assembly does not port unchanged: the slot roles moved.**  This is
-- what `dev/literature/level-formula-slot-roles.md:9` says a port must
-- re-derive, and it is re-derived here rather than copied.

-- THE ONE SYNTACTIC ROW THAT IS NOT DELIVERED.  The bounded graph
-- implies the machine graph, at the inner env x ∷ u ∷ v ∷ γ ∷ K, with
-- the graph's value at slot 0 and its index at slot 3.
-- [LJ-1.532]'s table row 6.
GraphAgree : Type (ℓ-suc ℓ)
GraphAgree =
  (x u v γ K : SL.S) (oγ : IsOrd (fst γ))
  → ⟨ (x ∷ u ∷ v ∷ γ ∷ K ∷ []) AbsL.⊨ᵐ LH0.LH.G.graphBndAt ⟩
  → ⟨ (x ∷ u ∷ v ∷ γ ∷ K ∷ []) AbsL.⊨ᵐ
       LsetGraphAt {5} zero (suc (suc (suc zero))) ⟩

-- The matrix decode at today's slots: from the bounded matrix at env
-- u ∷ v ∷ γ ∷ K, get `v = Lset γ`.  `ride-only` is delivered
-- (src/L/Condensation.lagda.md:422) and does the landing; the `≐`
-- conjunct carries the value from slot 0 to slot 1.
matrix-decode : (ga : GraphAgree) (u v γ K : SL.S) (oγ : IsOrd (fst γ))
              → ⟨ (u ∷ v ∷ γ ∷ K ∷ []) AbsL.⊨ᵐ LH0.matrix ⟩
              → fst v ≡ Lset (fst γ)
matrix-decode ga u v γ K oγ h =
  PT.rec (setIsSet (fst v) (Lset (fst γ))) go h
  where
  go : Σ[ x ∈ SL.S ]
         (⟨ x SL.∈ˢ K ⟩
        × ⟨ (x ∷ u ∷ v ∷ γ ∷ K ∷ []) AbsL.⊨ᵐ
             (LH0.LH.G.graphBndAt ∧̇ (var (suc (suc zero)) ≐ var zero)) ⟩)
     → fst v ≡ Lset (fst γ)
  go (x , x∈K , hx) =
    snd hx ∙
    ride-only {5} zero (suc (suc (suc zero)))
      (x ∷ u ∷ v ∷ γ ∷ K ∷ [])
      (ga x u v γ K oγ (fst hx)) oγ

-- The adequacy at a parameter index, and its decode.  This is the form
-- `levelIn` needs: the level AT the parameter, witnessed inside a bound.
Adeq : SL.S → Type (ℓ-suc ℓ)
Adeq m =
  ∥ Σ[ K' ∈ SL.S ] Σ[ u' ∈ SL.S ] Σ[ v' ∈ SL.S ]
    (⟨ v' SL.∈ˢ K' ⟩ × ⟨ (u' ∷ v' ∷ m ∷ K' ∷ []) AbsL.⊨ᵐ LH0.matrix ⟩) ∥₁

adeq-decode : (ga : GraphAgree) (m : SL.S) (om : IsOrd (fst m))
            → Adeq m
            → ∥ Σ[ K' ∈ SL.S ] Σ[ v' ∈ SL.S ]
                (⟨ v' SL.∈ˢ K' ⟩ × (fst v' ≡ Lset (fst m))) ∥₁
adeq-decode ga m om = PT.rec PT.squash₁ go
  where
  go : Σ[ K' ∈ SL.S ] Σ[ u' ∈ SL.S ] Σ[ v' ∈ SL.S ]
         (⟨ v' SL.∈ˢ K' ⟩ × ⟨ (u' ∷ v' ∷ m ∷ K' ∷ []) AbsL.⊨ᵐ LH0.matrix ⟩)
     → ∥ Σ[ K' ∈ SL.S ] Σ[ v' ∈ SL.S ]
         (⟨ v' SL.∈ˢ K' ⟩ × (fst v' ≡ Lset (fst m))) ∥₁
  go (K' , u' , v' , v∈K , h) =
    PT.∣ K' , v' , (v∈K , matrix-decode ga u' v' m K' om h) ∣₁

-- =====================================================================
-- SECTION 6.  `levelIn` IS STATED STRONGER THAN ITS ONLY CONSUMER ASKS.
--
--   MEASURED by grep over the master: `levelIn` is consumed at exactly
--   ONE site, src/L/BoundedSubset.lagda.md:1020, inside `Lβ⊆πX`, and
--   there it is applied at `sucV δ` and nowhere else.  `cover` has
--   three sites (:967, :1002, :1606) and they are general.
--
--   So the successor-only form below is everything the tree spends.
--   The implication that holds today is the trivial one; the direction
--   a supplier would want is the other, and it needs `Co`'s parameter
--   weakened in src/, which this brief does not fund.
-- =====================================================================

module AtHullWeak (lam : SV.S) (ordλ : IsOrd lam)
                  (succλ : (d : SV.S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
                  (X : SV.S)
                  (X⊆Lλ : (z : SV.S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
                  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  module A = AtHull lam ordλ succλ X X⊆Lλ ∅∈λ

  -- Everything src/ spends of `levelIn`, and no more.
  LevelInSuccOnly : Type (ℓ-suc ℓ)
  LevelInSuccOnly = (δ : SV.S) → IsOrd δ → ⟨ sucV δ ∈ˢ A.HS.C.πX ⟩
                  → ⟨ Lset (sucV δ) ∈ˢ A.HS.C.πX ⟩

  strong-gives-weak : A.LevelInH → LevelInSuccOnly
  strong-gives-weak li δ oδ s∈ = li (sucV δ) (suc-ord oδ) s∈

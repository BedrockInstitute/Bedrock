{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.533]  B9, `StageCountedCoded`: the stage injects into its own
-- index, AS AN L-CODED INJECTION.
--
-- VERDICT: NO-GO.  The obligation is NOT written in this file.  The
-- obstruction is agents/tasks/LJ-1-533/review-of-StageCountedCoded.md.
--
-- THIS FILE IS GREEN ON PURPOSE.  A hole would have made every
-- reduction below a claim; green makes each one a measurement.  What it
-- measures:
--
--   D-10.  The brief's type has NO `δ ∉ ω`.  Section 2 spends it and
--          lands the ambient statement at EVERY ordinal, finite ones
--          included.  The delivered chapter refuses exactly that: the
--          shadow binds `α ∉ ω` (src/L/StageCardinal.lagda.md:564-565)
--          and the finite branch lands in `ω`, not in `δ`
--          (src/L/StageCardinal.lagda.md:488-490).
--
--   W3.    NOTHING codes an arbitrary ambient injection.  Section 1
--          holds the direction the tree HAS (`readL`) and names the
--          direction it does NOT.  Refuted twice before this task:
--          agents/tasks/LJ-1-414/review-of-amb-to-coded.md and
--          agents/tasks/LJ-1-441/review-of-amb-to-coded-at-least.md.
--
--   THE BILL.  Section 4 reduces the CORRECTED target to exactly two
--          inputs: `AmbToCodeᵀ` at this one site, and the UNTRUNCATED
--          square-law family.  Nothing else is missing.
--
-- Nothing is postulated.  Nothing lands in src/.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-533.Probe533 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import V.Model {ℓ} using ( self∈sucV )
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd; isL; Lset )
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import L.Ordinal {ℓ} using ( #∈ω; numeral-ord; ω-ord )
open import L.Ordinal.SquareLaw {ℓ} lem using ( sq )
open import L.Cardinal {ℓ} lem using ( InjCode; _↪_ )
open import L.GCH {ℓ} lem using ( InjL )
open import L.CantorBernstein {ℓ} lem using ( readL )
import L.StageCardinal
import L.SquareLawClosed

open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( ω; sucV; #_ )
open import Cubical.Data.Sigma using ( _×_; Σ≡Prop )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))

module SV = hPropStructure 𝒮ᵥ
module SL = hPropStructure 𝒮ʟ

open SV using ( _∈ˢ_ )

-- `ordL` is DELIVERED, not rebuilt.  `[LJ-1.528]` is GO
-- (agents/tasks/LJ-1-528/lj-1.528-report.md:6) and the term is one line
-- at agents/tasks/LJ-1-528/Probe528.agda:93-94.
import LJ-1-528.Probe528
module P528 = LJ-1-528.Probe528 {ℓ} lem

-- =====================================================================
-- SECTION 0.  THE OBLIGATION'S TYPE, in the brief's own words.
--
--   NAMED, NOT INHABITED.  Sections 1 and 2 say why.
-- =====================================================================

StageCountedCodedᵀ : Type (ℓ-suc ℓ)
StageCountedCodedᵀ =
    (δ Lδ : SL.S) → IsOrd (fst δ) → (fst Lδ ≡ Lset (fst δ))
  → InjL Lδ δ

-- =====================================================================
-- SECTION 1.  W3, AND IT RAN FIRST.
--
--   THE WIDEST UNMEASURED TERM WAS ALREADY MEASURED, TWICE.  The brief
--   asks what turns an ambient function into an `InjCode`.  The answer
--   is NOTHING, and the tree already carries the two refutations.  This
--   section states both directions as types so the asymmetry is
--   checkable and not merely asserted.
-- =====================================================================

-- 1.1  THE DIRECTION THE TREE HAS.  `readL` (src/L/CantorBernstein.lagda.md:33-38)
-- reads an `InjCode` witness back as an ambient injection.  Code buys
-- ambient, and the truncation carries through by `PT.map`.
coded→ambient : (a b : SL.S) → InjL a b → ∥ ⟪ fst a ⟫ ↪ ⟪ fst b ⟫ ∥₁
coded→ambient a b = PT.map (readL a b)

-- 1.2  THE DIRECTION THE TREE DOES NOT HAVE.  This is `[LJ-1.414]`'s
-- `amb-to-coded` (agents/tasks/LJ-1-414/Probe414.agda:134-139) with its
-- site hypotheses dropped: the generic crossing.
--
-- IT IS NOT INHABITED IN THIS FILE AND IT IS NOT INHABITED IN THE TREE.
-- `_↪_` is a bare function with an injectivity proof
-- (src/L/Cardinal.lagda.md:47-48).  Every generator of an L-element set
-- is `hasSeparationL` (src/L/Axioms/Full.lagda.md:144) or
-- `hasReplacementL` (:277), and BOTH take a `Formula`.  An element of
-- `_↪_` carries no `Formula`.
AmbToCodeᵀ : Type (ℓ-suc ℓ)
AmbToCodeᵀ =
    (a b : SL.S) → ⟪ fst a ⟫ ↪ ⟪ fst b ⟫
  → ∥ Σ[ F ∈ SL.S ] InjCode F a b ∥₁

-- 1.3  AND THE TWO ARE NOT THE SAME STRENGTH.  Given the missing
-- direction, the delivered one is free; the converse composite is what
-- section 4 spends.
amb→coded→amb : AmbToCodeᵀ
              → (a b : SL.S) → ⟪ fst a ⟫ ↪ ⟪ fst b ⟫
              → ∥ ⟪ fst a ⟫ ↪ ⟪ fst b ⟫ ∥₁
amb→coded→amb amb a b f = coded→ambient a b (amb a b f)

-- =====================================================================
-- SECTION 2.  D-10.  THE BRIEF'S TYPE IS FALSE.
--
--   The brief binds `(δ Lδ : S) → IsOrd (fst δ) → ...` and NOTHING
--   ELSE.  No band membership, no infinitude.  The stage of an ordinal
--   is an L-element for free (`LsetS`, src/L/Axioms/Basic.lagda.md:160),
--   so the `Lδ` slot is not a restriction: `refl` fills it.
--
--   SPENDING THE TYPE THEREFORE LANDS THE AMBIENT STATEMENT AT EVERY
--   ORDINAL.  That is 2.2, and it typechecks.
-- =====================================================================

-- 2.1  The stage at an ordinal, as an L-element, with `fst` on the nose.
stageL : (δ : SL.S) → IsOrd (fst δ) → SL.S
stageL δ oδ = LsetS (fst δ) oδ

stageL-fst : (δ : SL.S) (oδ : IsOrd (fst δ)) → fst (stageL δ oδ) ≡ Lset (fst δ)
stageL-fst δ oδ = refl

-- 2.2  THE BRIEF'S TYPE, SPENT.  `readL` turns the coded conclusion back
-- into the ambient one, and NO hypothesis was added on the way.
brief→ambient :
    StageCountedCodedᵀ
  → (δ : SL.S) → IsOrd (fst δ) → ∥ ⟪ Lset (fst δ) ⟫ ↪ ⟪ fst δ ⟫ ∥₁
brief→ambient b δ oδ =
  coded→ambient (stageL δ oδ) δ (b δ (stageL δ oδ) oδ refl)

-- 2.3  AT EVERY NUMERAL.  `# n` is an ordinal (`numeral-ord`) and an
-- L-element (`ordL`), so the brief's type reaches the finite stages.
--
--   THE DELIVERED CHAPTER REFUSES THIS.  `stage-card-upper` binds
--   `⟨ α ∈ˢ ω ⟩ → Empty.⊥` (src/L/StageCardinal.lagda.md:564-565), and
--   at a finite δ the chapter's own branch goes to `ω` INSTEAD of to δ:
--   `fin-inj : (δ : S) → ⟨ δ ∈ˢ ω ⟩ → ⟪ Lset δ ⟫ ↪ ⟪ ω ⟫`
--   (src/L/StageCardinal.lagda.md:488-490).  A chapter that could land
--   `⟪ Lset δ ⟫ ↪ ⟪ δ ⟫` at a finite δ would not need that branch.
brief→ambient-at-numerals :
    StageCountedCodedᵀ
  → (n : ℕ) → ∥ ⟪ Lset (# n) ⟫ ↪ ⟪ # n ⟫ ∥₁
brief→ambient-at-numerals b n =
  brief→ambient b (P528.ordL (# n) (numeral-ord n)) (numeral-ord n)

-- =====================================================================
-- SECTION 3.  THE SHADOW, AND ITS TWO SIDE CONDITIONS.
--
--   `stage-card-upper` is NOT rebuilt here.  It is instantiated, which
--   is what a consumer must do, and the instantiation exposes what the
--   brief's binding cannot supply.
--
--   `α₀` IS A MODULE PARAMETER OF `L.StageCardinal`
--   (src/L/StageCardinal.lagda.md:16), not a constant.  It is the top
--   of a BAND: the theorem holds at every `α ∈ sucV α₀`.  So the first
--   side condition `⟨ α ∈ˢ sucV α₀ ⟩` is answerable at a single δ by
--   taking `α₀ := fst δ` and `self∈sucV` (src/V/Model.lagda.md:236),
--   and 3.2 does exactly that.  The second side condition, `α ∉ ω`, is
--   NOT answerable: it is section 2's finding.
-- =====================================================================

-- The square-law family `L.StageCardinal` binds, written out.
SqFamily : V ℓ → Type (ℓ-suc ℓ)
SqFamily α₀ = (δ : V ℓ) → ⟨ δ ∈ sucV α₀ ⟩ → (⟨ δ ∈ ω ⟩ → Empty.⊥) → sq δ

-- WHAT `src/` DELIVERS FOR IT, AND IT IS THE WRONG GRADE.
-- `sq-trunc-closed` (src/L/SquareLawClosed.lagda.md:325-328) has the
-- band and the infinitude at exactly these types.  ITS VALUE IS
-- TRUNCATED, and `L.StageCardinal` wants the untruncated Σ.
delivered-square :
    (α₀ : V ℓ) (oα₀ : IsOrd α₀)
  → (δ : V ℓ) → ⟨ δ ∈ sucV α₀ ⟩ → (⟨ δ ∈ ω ⟩ → Empty.⊥) → ∥ sq δ ∥₁
delivered-square α₀ oα₀ = SLC.sq-trunc-closed
  where module SLC = L.SquareLawClosed {ℓ} lem α₀ oα₀

module Shadow (α₀ : V ℓ) (oα₀ : IsOrd α₀) (sqf : SqFamily α₀) where

  module SC = L.StageCardinal {ℓ} lem α₀ oα₀ sqf

  -- 3.1  THE SHADOW ITSELF.  Instantiated, not rebuilt.  This is
  -- `[LJ-1.423]`'s `stub-upper` (agents/tasks/LJ-1-423/Probe423.agda:67-69)
  -- at this file's own binding.
  shadow : (δ : V ℓ) → IsOrd δ → ⟨ δ ∈ˢ sucV α₀ ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥)
         → ⟪ Lset δ ⟫ ↪ ⟪ δ ⟫
  shadow = SC.Upper.stage-card-upper

-- 3.2  THE FIRST SIDE CONDITION IS FREE AT ONE δ.  Take the band's top
-- to BE δ.  So the band is not what blocks B9.
shadow-at-self :
    (δ : V ℓ) (oδ : IsOrd δ) (sqf : SqFamily δ)
  → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥) → ⟪ Lset δ ⟫ ↪ ⟪ δ ⟫
shadow-at-self δ oδ sqf δ∉ω =
  Shadow.shadow δ oδ sqf δ oδ (self∈sucV δ) δ∉ω

-- =====================================================================
-- SECTION 4.  THE CORRECTED TARGET, AND THE WHOLE REMAINING BILL.
--
--   The brief's type minus section 2's falsity: the two side conditions
--   the delivered shadow carries, added back.
-- =====================================================================

StageCountedCoded′ᵀ : V ℓ → Type (ℓ-suc ℓ)
StageCountedCoded′ᵀ α₀ =
    (δ Lδ : SL.S) → IsOrd (fst δ)
  → ⟨ fst δ ∈ˢ sucV α₀ ⟩ → (⟨ fst δ ∈ˢ ω ⟩ → Empty.⊥)
  → (fst Lδ ≡ Lset (fst δ))
  → InjL Lδ δ

module Bill (α₀ : V ℓ) (oα₀ : IsOrd α₀) (sqf : SqFamily α₀) where

  open Shadow α₀ oα₀ sqf

  -- 4.1  THE REDUCTION.  Given the crossing of 1.2 at THIS site, the
  -- corrected target follows and nothing else is wanted.  So B9's whole
  -- remaining bill is `AmbToCodeᵀ` plus an untruncated `SqFamily`.
  reduce : AmbToCodeᵀ → StageCountedCoded′ᵀ α₀
  reduce amb δ Lδ oδ δ∈band δ∉ω e =
    subst (λ w → InjL w δ) (sym Lδ≡) (amb (stageL δ oδ) δ (shadow (fst δ) oδ δ∈band δ∉ω))
    where
    Lδ≡ : Lδ ≡ stageL δ oδ
    Lδ≡ = Σ≡Prop (λ v → snd (isL v)) e

  -- 4.2  AND THE CROSSING IS WANTED ONLY AT ONE PAIR, NOT GENERICALLY.
  -- The site is `a := Lset δ`, `b := δ`.  This is the type a successor
  -- brief should name instead of the generic 1.2.
  StageGraphᵀ : Type (ℓ-suc ℓ)
  StageGraphᵀ =
      (δ : SL.S) (oδ : IsOrd (fst δ))
    → ⟨ fst δ ∈ˢ sucV α₀ ⟩ → (⟨ fst δ ∈ˢ ω ⟩ → Empty.⊥)
    → ⟪ Lset (fst δ) ⟫ ↪ ⟪ fst δ ⟫
    → ∥ Σ[ F ∈ SL.S ] InjCode F (stageL δ oδ) δ ∥₁

  reduce-at-site : StageGraphᵀ → StageCountedCoded′ᵀ α₀
  reduce-at-site sg δ Lδ oδ δ∈band δ∉ω e =
    subst (λ w → InjL w δ) (sym Lδ≡)
      (sg δ oδ δ∈band δ∉ω (shadow (fst δ) oδ δ∈band δ∉ω))
    where
    Lδ≡ : Lδ ≡ stageL δ oδ
    Lδ≡ = Σ≡Prop (λ v → snd (isL v)) e

  -- 4.3  THE CONVERSE, FOR FREE.  The corrected target implies the
  -- ambient shadow, truncated.  So the coded statement is at least as
  -- strong as the delivered one, and no weakening happened above.
  corrected→ambient :
      StageCountedCoded′ᵀ α₀
    → (δ : SL.S) → IsOrd (fst δ)
    → ⟨ fst δ ∈ˢ sucV α₀ ⟩ → (⟨ fst δ ∈ˢ ω ⟩ → Empty.⊥)
    → ∥ ⟪ Lset (fst δ) ⟫ ↪ ⟪ fst δ ⟫ ∥₁
  corrected→ambient c δ oδ δ∈band δ∉ω =
    coded→ambient (stageL δ oδ) δ (c δ (stageL δ oδ) oδ δ∈band δ∉ω refl)

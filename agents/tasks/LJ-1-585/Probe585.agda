{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.585]  ARE ROWS 1 AND 4 THE SAME MISSING FORMULA?
--
-- W3 IS agents/tasks/LJ-1-585/runs/W3.agda AND IT WAS WRITTEN FIRST AND
-- TYPECHECKED ALONE, as the brief ordered.  Two runs, exit 0,
-- runs/w3-1.out (COLD) and runs/w3-2.out (WARM).  Its finding is
-- section 0.0 below.
--
-- THE ANSWER IN ONE LINE.  NO.  ONE FORMULA BUYS ONE ROW AND NOT TWO,
-- and the row it buys is not row 4 either: it is row 4 UNDER
-- `stage-card-upper`'s own two side conditions.  Row 1's residue sits
-- at an OFF-DIAGONAL pair, and what stands between it and row 4 is
-- exactly the obligation `[LJ-1.580]` could not build.
--
-- THIS FILE CARRIES NO HOLE AND NO POSTULATE, so every row in it is a
-- measurement and not a claim.  NOTHING LANDS IN `src/`.  Neither row
-- is built and no formula is built: `Def` is a hypothesis throughout.
--
--   Section 0.  D-10, THE TWO PAIRS.  Before anything else.
--   Section 1.  WHAT THE FORMULA BUYS.  Row 4, RESTRICTED.
--   Section 2.  AND IT IS NOT ROW 4.  The two side conditions, priced.
--   Section 3.  ROW 1's RESIDUE, AT THE GENERAL PAIR, AND THE GAP.
--   Section 4.  THE SITE.  The general shapes pinned to [LJ-1.580]'s
--               own names, so nothing above is a resemblance.
--   Section 5.  THE OBLIGATION.
--
-- CALIBER.  The program set GHCRTS="-A64m -I0 -M8g" on this pane.  I
-- did not set it.  One Agda process at a time.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open import L.Constructible using ( IsOrd )
import Cubical.Data.Empty as Empty

module LJ-1-585.Probe585 {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
  (α₀ : V ℓ) (oα₀ : IsOrd α₀)
  (sq : (δ : V ℓ) → ⟨ δ ∈ InfinitySet.sucV α₀ ⟩ → (⟨ δ ∈ InfinitySet.ω {ℓ} ⟩ → Empty.⊥)
      → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
          ((x y : ⟪ δ ⟫ × ⟪ δ ⟫) → f x ≡ f y → x ≡ y)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; Lset )
open import L.Ordinal {ℓ} using ( numeral-ord; #∈ω )
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import L.Cardinal {ℓ} lem using ( InjCode )
open import L.BoundedSubset {ℓ} lem using ( IsCardinal; _↪_ )
open import L.GCH {ℓ} lem using ( InjL )
open import L.InjChain {ℓ} lem using ( module InclGraph; module Comp )
import L.StageCardinal

open import V.Model {ℓ} using ( self∈sucV )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( _∪_; ⁅_⁆s )
open InfinitySet {ℓ} using ( ω; sucV; #_ )
open import Cubical.Data.Sigma using ( _×_; Σ≡Prop )
open import Cubical.Foundations.Prelude using ( subst2 )
import Cubical.Data.Nat as Nat
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )

module SV = hPropStructure 𝒮ᵥ
module SL = hPropStructure 𝒮ʟ

-- The delivered chapter, at this pane's parameters.  NOT rebuilt.
module SC = L.StageCardinal {ℓ} lem α₀ oα₀ sq

-- THE THREE PREDECESSORS.  Each probe is green and carries no hole, so
-- every type below is IMPORTED from the file that typechecked it and
-- none is transcribed.
import LJ-1-523.Probe523
import LJ-1-568.Probe568
import LJ-1-580.Probe580
module P523 = LJ-1-523.Probe523 {ℓ} lem
module P568 = LJ-1-568.Probe568 {ℓ} lem α₀ oα₀ sq
module P580 = LJ-1-580.Probe580 {ℓ} lem


-- ===================================================================
-- SECTION 0.  D-10, THE TWO PAIRS.
--
--   0.0  W3's FINDING, AND IT IS THE FRAME.  The two statements DO sit
--        in one file.  The price is that the file carries BOTH
--        parameter sets and neither statement uses the other's:
--        `L.StageCardinal`'s three (α₀, oα₀, sq;
--        src/L/StageCardinal.lagda.md:15-19), which row 1's residue
--        never mentions, AND `Devlin55.BoundedSubsetAt`'s seventeen
--        plus `Co`'s two (src/L/BoundedSubset.lagda.md:1385-1395,
--        :1555-1558), which row 4 never mentions.  Row 4 lives at
--        `{ℓ} (lem)` alone.  runs/w3-1.out, GREEN, 130.82 s COLD.
--
--   0.1  THE BRIEF ORDERS THE PAIR FIRST AND THIS IS IT.  The answer
--        comes in two halves, because Agda has no forward reference:
--        the DIAGONAL half is here, and the SITE half is section 4.2.
--        Neither half is a claim.  Both are terms.
-- ===================================================================

-- 0.1  ROW 4's PAIR IS THE DIAGONAL.  `StageCountedCoded`
--      (agents/tasks/LJ-1-523/Probe523.agda:258-261) quantifies over a
--      `δ` and an `Lδ` TIED to it by `fst Lδ ≡ Lset (fst δ)`, so at the
--      canonical choice the third argument is `refl` and the pair is
--      `(Lset d , d)`: ONE ordinal, twice.
row4-diagonal : P523.StageCountedCoded
              → (b : SL.S) (ob : IsOrd (fst b)) → InjL (LsetS (fst b) ob) b
row4-diagonal r4 b ob = r4 b (LsetS (fst b) ob) ob refl

-- 0.2  THE THREE SHAPES, NAMED ONCE.  Everything below is one of these
--      three, and section 4 pins each to the site's own term.
--
--      `Row4Shape` is row 4's conclusion at the diagonal pair.
--      `Row1Shape` is row 1's residue's pair, which [LJ-1.580] measured
--      to be `(Lset β , α)` (Probe580.agda:311-317): TWO ordinals.
--      `Gap` is `[LJ-1.580]`'s own unpaid obligation's conclusion
--      (Probe580.agda:292-293).
Row4Shape : (b : SL.S) → IsOrd (fst b) → Type (ℓ-suc ℓ)
Row4Shape b ob = InjL (LsetS (fst b) ob) b

Row1Shape : (b a : SL.S) → IsOrd (fst b) → Type (ℓ-suc ℓ)
Row1Shape b a ob = InjL (LsetS (fst b) ob) a

Gap : (b a : SL.S) → Type (ℓ-suc ℓ)
Gap b a = InjL b a

-- 0.3  AND THE ONE LINE THAT SAYS THE TWO SHAPES ARE THE SAME SHAPE
--      ONLY WHEN THE TWO ORDINALS ARE THE SAME ORDINAL.  This is D-10's
--      answer as a term and not as a reading of two pages: `Row1Shape`
--      at `a := b` IS `Row4Shape`, and nothing weaker does it.
row1-at-the-diagonal-is-row4 :
    (b : SL.S) (ob : IsOrd (fst b)) → Row1Shape b b ob ≡ Row4Shape b ob
row1-at-the-diagonal-is-row4 b ob = refl


-- ===================================================================
-- SECTION 1.  WHAT THE FORMULA BUYS.
--
--   THE HYPOTHESIS THE BRIEF NAMES, and it is taken and never built:
--   [LJ-1.568]'s `Def` (Probe568.agda:189-190) at `stage-card-upper`,
--   which is that file's own `B9-g` (Probe568.agda:144-147).
--
--   THE HYPOTHESIS CANNOT BE STATED MORE WIDELY THAN THE FUNCTION IT
--   IS ABOUT.  `stage-card-upper` (src/L/StageCardinal.lagda.md
--   :564-566) takes FOUR arguments, and two of them are side
--   conditions: `δ ∈ sucV α₀` and `δ ∉ ω`.  So `Def at
--   stage-card-upper` is silent wherever those fail, and section 2
--   prices that silence.
-- ===================================================================

DefAtSCU : Type (ℓ-suc ℓ)
DefAtSCU =
    (δ : V ℓ) (oδ : IsOrd δ) (δ∈suc : ⟨ δ ∈ˢ sucV α₀ ⟩)
  → (infδ : ⟨ δ ∈ˢ ω ⟩ → Empty.⊥)
  → P568.Def (LsetS δ oδ) (P568.ordS δ oδ) (fst (P568.B9-g δ oδ δ∈suc infδ))

-- Row 4 WITH `stage-card-upper`'s own two side conditions, and with
-- nothing else changed.  This is the row the formula reaches.
Row4Restricted : Type (ℓ-suc ℓ)
Row4Restricted =
    (δ : V ℓ) (oδ : IsOrd δ) → ⟨ δ ∈ˢ sucV α₀ ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥)
  → InjL (LsetS δ oδ) (P568.ordS δ oδ)

-- 1.1  AND THE FORMULA BUYS IT.  THIS IS NOT NEW WORK AND IT IS NOT
--      RESTATED: it is [LJ-1.568]'s `no-free-lunch-at-B9`
--      (Probe568.agda:454-463) at `H := Def`, IMPORTED.  The whole of
--      what this task adds at row 4 is the two transports of section 2.
def→row4-restricted : DefAtSCU → Row4Restricted
def→row4-restricted = P568.no-free-lunch-at-B9 P568.Def P568.def-restricted


-- ===================================================================
-- SECTION 2.  AND IT IS NOT ROW 4.
--
--   ROW 4 CARRIES NO SIDE CONDITION.  `StageCountedCoded` quantifies
--   over EVERY `δ : SL.S` with `IsOrd (fst δ)`
--   (Probe523.agda:258-261).  So the restricted row is a CONSEQUENCE of
--   row 4 and not row 4, and this section measures the difference
--   rather than describing it.
-- ===================================================================

-- 2.1  ONE DIRECTION HOLDS AND IT IS THE CHEAP ONE.  Row 4 in full
--      gives the restricted row by dropping the two conditions.
full→restricted : P523.StageCountedCoded → Row4Restricted
full→restricted r4 δ oδ _ _ = r4 (P568.ordS δ oδ) (LsetS δ oδ) oδ refl

-- 2.2  THE OTHER DIRECTION NEEDS THE TWO CONDITIONS AT EVERY ORDINAL,
--      AND THIS TERM IS EXACTLY THAT PRICE.  Nothing is hidden in it:
--      the two transports are `Σ≡Prop` over `isL`, which is an hProp.
restricted+conditions→full :
    Row4Restricted
  → ((δ : SL.S) → IsOrd (fst δ)
      → ⟨ fst δ ∈ˢ sucV α₀ ⟩ × (⟨ fst δ ∈ˢ ω ⟩ → Empty.⊥))
  → P523.StageCountedCoded
restricted+conditions→full r cond δ Lδ oδ e =
  subst2 InjL eL eδ (r (fst δ) oδ (fst (cond δ oδ)) (snd (cond δ oδ)))
  where
  eL : LsetS (fst δ) oδ ≡ Lδ
  eL = Σ≡Prop {A = SV.S} {B = λ w → ⟨ isL w ⟩} (λ w → snd (isL w)) (sym e)
  eδ : P568.ordS (fst δ) oδ ≡ δ
  eδ = Σ≡Prop {A = SV.S} {B = λ w → ⟨ isL w ⟩} (λ w → snd (isL w)) refl

-- 2.3  AND THAT PRICE IS NOT PAYABLE.  THE SUPPLY OF SECTION 2.2 IS
--      FALSE, at δ := 0, and the witness is one line of `src/`:
--      `#∈ω` (src/L/Ordinal.lagda.md:248-249) puts every numeral IN ω,
--      so no ordinal that is a numeral satisfies `δ ∉ ω`.
--
--      WHAT THIS DOES AND DOES NOT SAY.  It does NOT refute row 4.  It
--      says that `Def at stage-card-upper` does not reach row 4 BY THIS
--      ROUTE, because the hypothesis is not even STATED at a finite δ.
--      [LJ-1.533]'s review says in its own words that it "did not prove
--      `⟪ Lset δ ⟫ ↪ ⟪ δ ⟫` false in Agda at any named finite δ"
--      (agents/tasks/LJ-1-533/review-of-StageCountedCoded.md:54-55), and
--      this file does not prove it either.
side-conditions-are-false :
    ((δ : SL.S) → IsOrd (fst δ)
      → ⟨ fst δ ∈ˢ sucV α₀ ⟩ × (⟨ fst δ ∈ˢ ω ⟩ → Empty.⊥))
  → Empty.⊥
side-conditions-are-false cond =
  snd (cond (P568.ordS (# Nat.zero) (numeral-ord Nat.zero))
            (numeral-ord Nat.zero))
      (#∈ω Nat.zero)


-- ===================================================================
-- SECTION 3.  ROW 1's RESIDUE, AT THE GENERAL PAIR, AND THE GAP.
--
--   THE QUESTION THE BRIEF ASKS IS WHETHER ONE PAYMENT CLEARS TWO ROWS.
--   The two rows below answer it in both directions, and neither uses
--   the bounded-subset site: they hold at ANY pair of L-ordinals, so
--   the answer is not an accident of where the residue happens to sit.
--
--   `Comp` (src/L/InjChain.lagda.md:314-433) composes two coded
--   injections; `InclGraph` (:575-598) codes any inclusion between two
--   L-elements.  Both are IMPORTED and neither is rebuilt.
-- ===================================================================

-- 3.1  ROW 4 AT b, PLUS A CODE FOR b ↪ a, GIVES ROW 1's SHAPE.  So the
--      residue is REACHABLE from row 4, and what it costs on top is one
--      named thing.
row4+gap→row1 :
    (b a : SL.S) (ob : IsOrd (fst b))
  → Row4Shape b ob → Gap b a → Row1Shape b a ob
row4+gap→row1 b a ob = PT.map2 step
  where
  step : Σ[ F ∈ SL.S ] InjCode F (LsetS (fst b) ob) b
       → Σ[ H ∈ SL.S ] InjCode H b a
       → Σ[ K ∈ SL.S ] InjCode K (LsetS (fst b) ob) a
  step (F , (svF , dmF , ijF , ranF)) (H , (svH , dmH , ijH , ranH)) =
    K.K , (K.svK , K.dmK , K.ijK , K.ranK)
    where
    module K = Comp (LsetS (fst b) ob) b a F H
                 svF dmF ijF ranF svH dmH ijH ranH

-- 3.2  AND BACK, WITH NO ROW 4 AT ALL.  Row 1's shape GIVES the gap,
--      because b ⊆ Lset b is an inclusion (`Lower.α⊆Lset`,
--      src/L/StageCardinal.lagda.md:193-195) and the tree codes those.
--
--      THIS IS THE ROW THAT SETTLES THE BRIEF'S QUESTION.  Paying row
--      1's residue PAYS [LJ-1.580]'s obligation.  A payment that
--      discharges an obligation a predecessor measured to be blocked on
--      that route is not a payment row 4 makes for free.
row1→gap :
    (b a : SL.S) (ob : IsOrd (fst b))
  → Row1Shape b a ob → Gap b a
row1→gap b a ob = PT.map step
  where
  module Ib = InclGraph b (LsetS (fst b) ob) (SC.Lower.α⊆Lset (fst b) ob)
  step : Σ[ H ∈ SL.S ] InjCode H (LsetS (fst b) ob) a
       → Σ[ K ∈ SL.S ] InjCode K b a
  step (H , (svH , dmH , ijH , ranH)) =
    K.K , (K.svK , K.dmK , K.ijK , K.ranK)
    where
    module K = Comp b (LsetS (fst b) ob) a Ib.G H
                 Ib.sv Ib.dm Ib.ij Ib.ran svH dmH ijH ranH


-- ===================================================================
-- SECTION 4.  THE SITE.
--
--   SECTION 3 IS ABOUT A SHAPE.  THIS SECTION SAYS THE SHAPE IS THE
--   SITE'S OWN STATEMENT, so nothing above rests on a resemblance.
--   [LJ-1.577] asserted a resemblance about these very objects and
--   [LJ-1.580] measured it wrong
--   (agents/tasks/LJ-1-580/review-of-beta-into-alpha-coded.md:40).
--
--   The telescope is [LJ-1.580]'s `Site` and `CoAt`, verbatim
--   (Probe580.agda:118-131, :157-166), because those two modules are
--   where the residue is named.
-- ===================================================================

module AtTheSite
  (κᴸ : SL.S) (ordκ : IsOrd (fst κᴸ)) (cardκ : IsCardinal (fst κᴸ))
  (κ∉ω : ⟨ fst κᴸ ∈ˢ ω ⟩ → Empty.⊥)
  (α : SV.S) (ordα : IsOrd α) (α∈κ : ⟨ α ∈ˢ fst κᴸ ⟩)
  (α∉ω : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
  (sqα : (δ : SV.S) → ⟨ δ ∈ˢ sucV α ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥)
       → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
           ((u v : ⟪ δ ⟫ × ⟪ δ ⟫) → f u ≡ f v → u ≡ v))
  (x : SV.S) (x⊆Lα : (z : SV.S) → ⟨ z ∈ˢ x ⟩ → ⟨ z ∈ˢ Lset α ⟩)
  (absorbs : ⟪ Lset α ∪ ⁅ x ⁆s ⟫ ↪ ⟪ Lset α ⟫)
  (lam : SV.S) (ordλ : IsOrd lam) (α∈λ : ⟨ α ∈ˢ lam ⟩)
  (succλ : (d : SV.S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (x∈Lλ : ⟨ x ∈ˢ Lset lam ⟩)
  where

  module S580 = P580.Site κᴸ ordκ cardκ κ∉ω α ordα α∈κ α∉ω sqα x x⊆Lα
                          absorbs lam ordλ α∈λ succλ x∈Lλ

  module Co
    (levelIn : (δ : SV.S) → IsOrd δ → ⟨ δ ∈ˢ S580.BSA.HS.C.πX ⟩
             → ⟨ Lset δ ∈ˢ S580.BSA.HS.C.πX ⟩)
    (cover : (y : SV.S) → ⟨ y ∈ˢ S580.BSA.HS.M ⟩
           → ∥ Σ[ γ ∈ SV.S ]
                ( IsOrd γ × ⟨ γ ∈ˢ S580.BSA.HS.C.πX ⟩
                × ⟨ S580.BSA.HS.C.π y ∈ˢ Lset γ ⟩ ) ∥₁)
    where

    module C580 = S580.CoAt levelIn cover

    -- 4.1  THE TWO ORDINALS ARE TWO, AND THE SITE BINDS THEM
    --      SEPARATELY.  β is `Cn.condenses .fst`
    --      (src/L/BoundedSubset.lagda.md:1562-1563) and α is the
    --      module's own parameter (Probe580.agda:121).  The site
    --      delivers `β ∈ κ` (src/L/BoundedSubset.lagda.md:1594) and
    --      `α ∈ κ` (Probe580.agda:121), and NO relation between the
    --      two.  These two ascriptions are the elaborator's word for
    --      that, and not a reading of the page.
    two-ordinals : SV.S × SV.S
    two-ordinals = C580.C.β , α

    beta-is-not-alpha-by-any-row-of-the-site :
      ⟨ C580.C.β ∈ˢ fst κᴸ ⟩ × ⟨ α ∈ˢ fst κᴸ ⟩
    beta-is-not-alpha-by-any-row-of-the-site = C580.C.β∈κ , α∈κ

    -- 4.1a  AND THE SITE'S OWN TOWER IS NOT THIS FILE'S TOWER.
    --       `BoundedSubsetAt` builds its own `L.StageCardinal` at ITS α
    --       (src/L/BoundedSubset.lagda.md:1397), so the site's
    --       `stage-card-upper` takes `γ ∈ sucV α` and NOT `γ ∈ sucV α₀`.
    --       The type below is the elaborator's word for that.  Section
    --       1's `DefAtSCU` is stated at α₀ and is therefore not even
    --       ABOUT the function the site applies.
    site-tower-is-alpha :
        (γ : SV.S) → IsOrd γ → ⟨ γ ∈ˢ sucV α ⟩ → (⟨ γ ∈ˢ ω ⟩ → Empty.⊥)
      → ⟪ Lset γ ⟫ ↪ ⟪ γ ⟫
    site-tower-is-alpha = S580.BSA.stage-card-upper

    -- 4.1b  AND THE SITE APPLIES IT AT ONE ARGUMENT ONLY, WHICH IS α.
    --       `code-inj` is `comp-inj absorbs (stage-card-upper α ...)`
    --       (src/L/BoundedSubset.lagda.md:1512-1513), so the ambient
    --       injection the brief names supplies the DIAGONAL pair
    --       `(Lset α , α)` here.  THAT IS A THIRD PAIR, and it is not
    --       row 1's residue's pair either.
    site-scu-is-at-alpha : ⟪ Lset α ⟫ ↪ ⟪ α ⟫
    site-scu-is-at-alpha = S580.BSA.stage-card-upper α ordα (self∈sucV α) α∉ω

    -- 4.2  D-10's OTHER HALF.  ROW 1's RESIDUE IS AT `(Lset β , α)`.
    --      [LJ-1.580]'s own identification, IMPORTED and not re-derived
    --      (Probe580.agda:311-317).
    row1-pair :
      C580.Leg2Coded
        ≡ InjL (Lset C580.C.β , P580.Lset-isL C580.C.β C580.C.β-isOrd) S580.αᴸ
    row1-pair = C580.residue-is-a-stage-bound

    -- 4.3  AND SECTION 3's SHAPE IS THAT RESIDUE.  The only difference
    --      is which proof of `isL (Lset β)` the pair carries: `src/`'s
    --      own `isL-Lset` (src/L/Axioms/Basic.lagda.md:156-161) inside
    --      `LsetS`, or [LJ-1.580]'s rebuilt `Lset-isL`
    --      (Probe580.agda:104-109).  `isL` is an hProp, so they agree.
    shape-is-the-residue :
      Row1Shape C580.βᴸ S580.αᴸ C580.C.β-isOrd ≡ C580.Leg2Coded
    shape-is-the-residue =
      cong (λ w → InjL w S580.αᴸ)
        (Σ≡Prop {A = SV.S} {B = λ w → ⟨ isL w ⟩} (λ w → snd (isL w))
          {u = LsetS C580.C.β C580.C.β-isOrd}
          {v = Lset C580.C.β , P580.Lset-isL C580.C.β C580.C.β-isOrd} refl)
      ∙ sym row1-pair

    -- 4.4  AND SECTION 3's GAP IS [LJ-1.580]'s OBLIGATION.  Its type,
    --      verbatim (Probe580.agda:292-293): the obligation is the gap
    --      with the ambient injection to its left.
    gap-is-580s-obligation :
      C580.BetaIntoAlphaCoded
        ≡ ((⟪ C580.C.β ⟫ ↪ ⟪ α ⟫) → Gap C580.βᴸ S580.αᴸ)
    gap-is-580s-obligation = refl

    -- 4.5  SO AT THE SITE: ROW 4 AT β BUYS THE RESIDUE ONLY WITH THE
    --      GAP, AND THE RESIDUE BUYS THE GAP BACK.
    site-row4+gap→residue :
      Row4Shape C580.βᴸ C580.C.β-isOrd → Gap C580.βᴸ S580.αᴸ → C580.Leg2Coded
    site-row4+gap→residue r g =
      subst (λ T → T) shape-is-the-residue
        (row4+gap→row1 C580.βᴸ S580.αᴸ C580.C.β-isOrd r g)

    -- Section 3.2's general route, at the site.  It lands where
    -- [LJ-1.580]'s own `leg2-coded→at-β` lands (Probe580.agda:245),
    -- and 4.7 says the two agree.
    site-residue→gap : C580.Leg2Coded → Gap C580.βᴸ S580.αᴸ
    site-residue→gap h =
      row1→gap C580.βᴸ S580.αᴸ C580.C.β-isOrd
        (subst (λ T → T) (sym shape-is-the-residue) h)

    -- 4.6  AND ROW 4 IN FULL DOES NOT CLOSE THE SITE EITHER.  Row 4
    --      applied at β is `Row4Shape`, and 4.5 says it still wants the
    --      gap.  THIS IS THE BRIEF'S QUESTION, ANSWERED AT THE SITE.
    row4-in-full-still-wants-the-gap :
      P523.StageCountedCoded → Gap C580.βᴸ S580.αᴸ → C580.Leg2Coded
    row4-in-full-still-wants-the-gap r4 =
      site-row4+gap→residue (row4-diagonal r4 C580.βᴸ C580.C.β-isOrd)

    -- 4.7  AND THE SITE'S OWN TERM AGREES WITH SECTION 3.2's, so this
    --      file's general route is not a neighbour of [LJ-1.580]'s.
    --      `leg2-coded→at-β` is IMPORTED.
    the-two-routes-have-one-type :
      (C580.Leg2Coded → Gap C580.βᴸ S580.αᴸ) × (C580.Leg2Coded → Gap C580.βᴸ S580.αᴸ)
    the-two-routes-have-one-type = site-residue→gap , C580.leg2-coded→at-β


-- ===================================================================
-- SECTION 5.  THE OBLIGATION.
--
--   THE BRIEF ASKED FOR ONE TERM: `Def at stage-card-upper` implies
--   row 1's residue AND row 4, "or, if one of the two does not follow,
--   the term that says which and why".  NEITHER FOLLOWS AS STATED, and
--   the three components say which and why.
--
--     1.  WHAT THE FORMULA BUYS.  Row 4 under `stage-card-upper`'s own
--         two side conditions.  Section 1.1.
--     2.  AND THAT IS NOT ROW 4.  It is a CONSEQUENCE of row 4, and
--         section 2.3 proves the way back is not payable.
--     3.  AND ROW 1's RESIDUE IS NOT A SECOND INSTANCE OF ROW 4.  At
--         any pair of L-ordinals, the residue's shape is row 4's shape
--         COMPOSED with the gap, and the residue IMPLIES the gap on its
--         own.  Section 4 pins both to [LJ-1.580]'s own names.
--
--   SO ONE PAYMENT CLEARS ONE ROW AT MOST, NOT TWO, AND THE BILL DOES
--   NOT DROP TO THREE.
-- ===================================================================

one-formula-two-rows :
    DefAtSCU
  → Row4Restricted
  × ( P523.StageCountedCoded → Row4Restricted )
  × ( (b a : SL.S) (ob : IsOrd (fst b))
      → (Row4Shape b ob → Gap b a → Row1Shape b a ob)
      × (Row1Shape b a ob → Gap b a) )
one-formula-two-rows d =
    def→row4-restricted d
  , ( full→restricted
    , (λ b a ob → row4+gap→row1 b a ob , row1→gap b a ob) )

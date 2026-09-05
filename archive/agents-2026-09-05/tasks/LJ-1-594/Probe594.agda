{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.594]  WHAT A DEFINABLE PAIRING WOULD COST `L.StageCardinal`.
--
-- VERDICT: NO-GO.  `agents/tasks/LJ-1-594/review-of-pairing-suffices.md`
-- states it.  **THE OBLIGATION `pairing-suffices` IS NOT IN THIS FILE**
-- and no weaker term is offered as one.  This file carries NO hole and
-- NO postulate, so every reduction in it is a measurement and not a
-- claim.  Nothing lands in `src/`.
--
-- W3 IS agents/tasks/LJ-1-594/runs/W3.agda AND IT WAS WRITTEN FIRST AND
-- TYPECHECKED ALONE (`runs/w3-2.out`, GREEN, 1.06 s).  It is IMPORTED
-- below, not restated.
--
--   Section 0.  D-10, BEFORE ANY OTHER AGDA.  `sq` at its site, and the
--               target's truth.  The target is NOT refutable here.
--   Section 1.  W3, IMPORTED.  What the parameter carries.
--   Section 2.  THE PAIRING, STATED.  As weakly as I can write it.
--   Section 3.  THE MEASUREMENT.  `class-pred` HAS FIVE INGREDIENTS AND
--               THE PAIRING IS ONLY ONE OF THEM.  This corrects the
--               sentence the brief quotes from `[LJ-1.584]`.
--   Section 4.  WHAT THE TREE ALREADY HAS, re-ascribed, so the next
--               brief can take it: the recursion is NOT the block.
--
-- CALIBER.  The program set GHCRTS="-A64m -I0 -M8g" on this pane.  I did
-- not set it.  One Agda process at a time.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open import L.Constructible using ( IsOrd )
import Cubical.Data.Empty as Empty
open import LJ-1-594.runs.W3 using ( SqParam )

module LJ-1-594.Probe594 {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
  (α₀ : V ℓ) (oα₀ : IsOrd α₀) (sq : SqParam α₀) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
import FOL.Absoluteness
import FOL.ZFModel
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; Lset; 𝒟ₒ; 𝒟ₒ-inv )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import L.GCH {ℓ} lem using ( InjL )
open import L.Cardinal {ℓ} lem using ( _↪_ )
open import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ} using ( leastOf )
open import L.Recursion {ℓ} lem using ( Definition; Recursion; asRecursion; module Of )
open import L.Hierarchy {ℓ} lem using ( IsHier; hierL; hierL-spec )
open import L.Coding.CodeSet {ℓ} lem using ( keyS; AllCodes; key∈AllCodes )
import L.StageCardinal

open import Cubical.Data.Nat using ( ℕ )
open import Cubical.Data.Sigma using ( _×_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫↪ )
open InfinitySet {ℓ} using ( sucV; ω )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
module SV = hPropStructure 𝒮ᵥ
module SL = hPropStructure 𝒮ʟ
open SV using ( _∈ˢ_ )
open SL using ( S )

module ModelL = FOL.ZFModel 𝒮ʟ
module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- The delivered chapter, at this pane's parameters.  NOT rebuilt.
module SC = L.StageCardinal {ℓ} lem α₀ oα₀ sq

-- THE PREDECESSORS THIS FILE STANDS ON.  Each probe is green and carries
-- no hole, so every type below is IMPORTED from the file that
-- typechecked and none is transcribed.
import LJ-1-561.Probe561 {ℓ} lem α₀ oα₀ sq as P561
import LJ-1-568.Probe568 {ℓ} lem α₀ oα₀ sq as P568
import LJ-1-584.Probe584 {ℓ} lem α₀ oα₀ sq as P584
import LJ-1-584.runs.W3a {ℓ} lem α₀ oα₀ sq as W3a


-- ===================================================================
-- SECTION 0.  D-10, BEFORE ANY OTHER AGDA.
--
--   THE BRIEF ORDERS IT: "D-10, BEFORE ANY AGDA, AND IT IS `sq` AT ITS
--   SITE."
--
--   `sq` IS DECLARED ONCE AND USED ONCE.  The declaration is
--   src/L/StageCardinal.lagda.md:17-20, the module header's third
--   parameter.  The ONLY other occurrence of the name in that file is
--   src/L/StageCardinal.lagda.md:283,
--
--       module B = Bound α oα infα (sq α α∈suc infα)
--
--   inside `module LimitStep` (:277).  Measured by `grep -nw "sq"`,
--   which returns exactly those two lines; `grep -cw` returns 2.  NO
--   COMMAND WITH `head` WAS USED TO REACH THAT COUNT.  The other seven
--   matches of the substring in that file are `squash₁` (:51, :323,
--   :327, :445) and the word "square" in a comment (:59).
--
--   THE CALLERS ARE COUNTED IN THE REPORT'S `## WHAT SUBSTITUTING IT
--   WOULD COST src/` and are not Agda.
--
--   THE QUESTION D-10 ASKS IS WHETHER THE TARGET IS TRUE.  The rows
--   below answer it, and neither is a reading.
-- ===================================================================

-- 0.1  THE TARGET, IMPORTED AND NOT RESTATED.  `Reopener` is
--      [LJ-1.584]'s (Probe584.agda:250-251), which is
--      `InjL (LsetS α oα) (ordS α oα)`, `src/L/GCH.lagda.md:38`.
Target : (α : V ℓ) → IsOrd α → Type (ℓ-suc ℓ)
Target = P584.Reopener

-- 0.2  THE ROUTE FROM A FORMULA TO THE TARGET IS ALREADY IN THE TREE,
--      AND IT COSTS NOTHING.  `restrict→B9` is [LJ-1.568]'s
--      (Probe568.agda:285-292) and `def-restricted` is its THEOREM
--      (Probe568.agda:252-253), so no hypothesis is spent here.
--      **THIS IS THE WHOLE OF ROUTE 2's SECOND HALF**: whoever produces
--      a formula for the injection gets the target for free.
def-h→target :
    (α : V ℓ) (oα : IsOrd α) (α∈suc : ⟨ α ∈ˢ sucV α₀ ⟩)
    (α∉ω : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
  → P584.Obligation α oα α∈suc α∉ω
  → Target α oα
def-h→target = P568.restrict→B9 P568.Def P568.def-restricted

-- 0.3  SO THE TARGET IS NOT REFUTABLE HERE.  `V = L` gives it, through
--      [LJ-1.584]'s `vl→obligation` (Probe584.agda:108-118) and 0.2.
--      Nothing on that path is truncated before `InjL`'s own
--      truncation.
vl→target : ((x : V ℓ) → ⟨ isL x ⟩)
          → (α : V ℓ) (oα : IsOrd α) (α∈suc : ⟨ α ∈ˢ sucV α₀ ⟩)
            (α∉ω : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
          → Target α oα
vl→target vl α oα α∈suc α∉ω =
  def-h→target α oα α∈suc α∉ω (P584.vl→obligation vl α oα α∈suc α∉ω)

-- 0.4  AND A REFUTATION OF THE TARGET IS A REFUTATION OF `V = L`.
--      That is 0.3 contraposed and nothing more.  **THIS FILE
--      THEREFORE DOES NOT CLAIM THE TARGET IS FALSE.**  It measures
--      what a definable pairing does and does not buy.
refuting-target-refutes-V=L :
    (α : V ℓ) (oα : IsOrd α) (α∈suc : ⟨ α ∈ˢ sucV α₀ ⟩)
    (α∉ω : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
  → (Target α oα → Empty.⊥)
  → ((x : V ℓ) → ⟨ isL x ⟩) → Empty.⊥
refuting-target-refutes-V=L α oα α∈suc α∉ω no vl =
  no (vl→target vl α oα α∈suc α∉ω)


-- ===================================================================
-- SECTION 1.  W3, IMPORTED.
--
--   `runs/W3.agda` re-ascribes the parameter's type ALONE and shows
--   `L.StageCardinal` accepts it (runs/W3.agda:39-40).  THIS FILE'S
--   OWN `sq` IS OF THAT TYPE: the module header above says so, and the
--   application `SC` above elaborates.  So the transcription is checked
--   and not quoted.
--
--   WHAT THE PARAMETER CARRIES: one function on the pairs of members of
--   δ and one injectivity proof of it (runs/W3.agda:47-58).  NO
--   `Formula`, no L-set, no satisfaction, no ordinal grade.
-- ===================================================================

sq-param-type : Type (ℓ-suc ℓ)
sq-param-type = SqParam α₀


-- ===================================================================
-- SECTION 2.  THE PAIRING, STATED.
--
--   THE BRIEF: "State the pairing hypothesis yourself.  Naming it is
--   the deliverable", and "STATE THE PAIRING AS WEAKLY AS YOU CAN."
--
--   `DefPairing` below is the weakest form I can write.  It says: SOME
--   formula of the object language, with L-sets as constants, describes
--   the module's own pairing at α, in both directions, on the members
--   of α.  It is the shape [LJ-1.554]'s `LinkAt` (Probe554.agda:80-87)
--   takes for a UNARY assignment, at arity two.
--
--   WHAT IT ASSUMES, AND HOW LITTLE.
--     * NO LEVY GRADE.  The formula is arbitrary, exactly as
--       [LJ-1.568]'s `Def` is (Probe568.agda:189-190), because the
--       separation it is spent through takes an arbitrary formula
--       (src/L/Axioms/Full.lagda.md:144).
--     * IT DESCRIBES THE PAIRING THE MODULE ALREADY HAS.  It does not
--       ask for a new one, and it does not ask the pairing to be
--       canonical.
--     * IT IS ABOUT ONE α.  Nothing is assumed at any other stage.
--     * IT IS UNTRUNCATED, which is the STRONGEST reading of the three
--       possible ones, and section 3 shows the file does not need the
--       difference: the hypothesis is not sufficient in either grade.
-- ===================================================================

DefPairing : (α : V ℓ) (oα : IsOrd α) → ⟨ α ∈ˢ sucV α₀ ⟩
           → (⟨ α ∈ˢ ω ⟩ → Empty.⊥) → Type (ℓ-suc ℓ)
DefPairing α oα α∈suc α∉ω =
  Σ[ Pf ∈ Formula S 3 ]
    ( ((x y : ⟪ α ⟫) → ⟨ (asL (pr2 x y) ∷ asL x ∷ asL y ∷ []) ⊨ Pf ⟩)
    × ((x y : ⟪ α ⟫) (z : S) → ⟨ (z ∷ asL x ∷ asL y ∷ []) ⊨ Pf ⟩
         → z ≡ asL (pr2 x y)) )
  where
  asL : ⟪ α ⟫ → S
  asL = P561.up (P568.ordS α oα)
  pr2 : ⟪ α ⟫ → ⟪ α ⟫ → ⟪ α ⟫
  pr2 x y = fst (sq α α∈suc α∉ω) (x , y)


-- ===================================================================
-- SECTION 3.  THE MEASUREMENT.
--
--   THE BRIEF QUOTES `[LJ-1.584]`: "class-pred's other two ingredients
--   are already internal ... THE PAIRING IS [the only non-internal
--   part]."  **THAT SENTENCE UNDERCOUNTS THE INGREDIENTS, AND THIS
--   SECTION IS THE COUNT.**  Every row is `refl`.
-- ===================================================================

-- 3.1  THE TWO INGREDIENTS THE PREDECESSOR NAMED AS INTERNAL ARE
--      INTERNAL, AND HERE THAT IS A THEOREM AND NOT A READING.  At the
--      real site, `limit-step` (src/L/StageCardinal.lagda.md:396-403)
--      supplies `D := DefOf.defSet (Lset ·)` (:400) and `inv := 𝒟ₒ-inv`
--      (:401).  Both are `L.Constructible`'s, so both are internal.
D-at-the-site :
    (α : V ℓ) (α∈suc : ⟨ α ∈ˢ sucV α₀ ⟩) (oα : IsOrd α)
    (infα : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
    (ih : (m : ⟪ α ⟫) → ⟪ Lset (⟪ α ⟫↪ m) ⟫ ↪ ⟪ α ⟫)
  → fst (SC.limit-step α α∈suc oα infα ih)
    ≡ SC.LimitStep.h α α∈suc oα infα (λ δ φ → DefOf.defSet (Lset δ) φ)
        (λ δ x h → 𝒟ₒ-inv (Lset δ) x h) ih
D-at-the-site _ _ _ _ _ = refl

-- 3.2  AND THE PAIRING INGREDIENT IS `sq` APPLIED AND NOTHING ELSE.
--      `pair-is-sq` is [LJ-1.584]'s W3 (runs/W3a.agda:41-46), IMPORTED.
pair-is-sq :
    (α : V ℓ) (oα : IsOrd α) (α∈suc : ⟨ α ∈ˢ sucV α₀ ⟩)
    (infα : ⟨ α ∈ˢ ω ⟩ → Empty.⊥) (x y : ⟪ α ⟫)
  → SC.Bound.pair α oα infα (sq α α∈suc infα) x y
    ≡ fst (sq α α∈suc infα) (x , y)
pair-is-sq = W3a.pair-is-sq


-- 3.3  **THE THIRD INGREDIENT, AND THE PREDECESSOR DID NOT COUNT IT.**
--      `cnt` (src/L/StageCardinal.lagda.md:288-289) is the counting of
--      the formulas of the stage BELOW, and it is computed from the
--      module's fifth argument `ih`.  That argument is not internal,
--      not internalisable by the pairing, and not mentioned by the
--      route-2 sentence the brief quotes.
cnt-is-the-IH :
    (α : V ℓ) (α∈suc : ⟨ α ∈ˢ sucV α₀ ⟩) (oα : IsOrd α)
    (infα : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
    (D : (δ : V ℓ) → Formula ⟪ Lset δ ⟫ 1 → V ℓ)
    (inv : (δ : V ℓ) (y : V ℓ) → ⟨ y ∈ˢ 𝒟ₒ (Lset δ) ⟩
         → ∥ Σ[ φ₀ ∈ Formula ⟪ Lset δ ⟫ 1 ] (D δ φ₀ ≡ y) ∥₁)
    (ih : (m : ⟪ α ⟫) → ⟪ Lset (⟪ α ⟫↪ m) ⟫ ↪ ⟪ α ⟫)
    (m : ⟪ α ⟫) (φ : Formula ⟪ Lset (⟪ α ⟫↪ m) ⟫ 1)
  → SC.LimitStep.cnt α α∈suc oα infα D inv ih m φ
    ≡ fst (SC.Bound.formula-bound α oα infα (sq α α∈suc infα)
             {K = ⟪ Lset (⟪ α ⟫↪ m) ⟫} (ih m)) φ
cnt-is-the-IH _ _ _ _ _ _ _ _ _ = refl

-- 3.4  **THE COUNT, IN ONE ROW.**  `class-pred`
--      (src/L/StageCardinal.lagda.md:319-324) written out with the
--      pairing already replaced by `sq` applied.  READ THE RIGHT HAND
--      SIDE AND COUNT WHAT A FORMULA WOULD HAVE TO DESCRIBE:
--
--        (i)   `D`, the definable power set.  INTERNAL, by 3.1.
--        (ii)  the ordinal order, in `leastOf` below.  INTERNAL, by 3.5.
--        (iii) `fst (sq α α∈suc infα)`, the pairing.  THE HYPOTHESIS.
--        (iv)  `ih m`, the injection at the stage BELOW.  NOT INTERNAL
--              and NOT the pairing.  3.6 says what it is at the real
--              site.
--        (v)   `Formula ⟪ Lset (⟪ α ⟫↪ m) ⟫ 1`, the META syntax over an
--              AMBIENT carrier, which the quantifier `Σ[ φ ∈ ... ]`
--              ranges over.  A formula of the OBJECT language cannot
--              quantify over it without a coded copy of it inside L.
--
--      SO THE INGREDIENTS ARE FIVE, NOT THREE, AND THE PAIRING IS ONE
--      OF THEM.
class-pred-is :
    (α : V ℓ) (α∈suc : ⟨ α ∈ˢ sucV α₀ ⟩) (oα : IsOrd α)
    (infα : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
    (D : (δ : V ℓ) → Formula ⟪ Lset δ ⟫ 1 → V ℓ)
    (inv : (δ : V ℓ) (y : V ℓ) → ⟨ y ∈ˢ 𝒟ₒ (Lset δ) ⟩
         → ∥ Σ[ φ₀ ∈ Formula ⟪ Lset δ ⟫ 1 ] (D δ φ₀ ≡ y) ∥₁)
    (ih : (m : ⟪ α ⟫) → ⟪ Lset (⟪ α ⟫↪ m) ⟫ ↪ ⟪ α ⟫)
    (x : ⟪ Lset α ⟫) (y : ⟪ α ⟫)
  → SC.LimitStep.class-pred α α∈suc oα infα D inv ih x y
    ≡ ( ∥ Σ[ m ∈ ⟪ α ⟫ ] Σ[ φ ∈ Formula ⟪ Lset (⟪ α ⟫↪ m) ⟫ 1 ]
            ( ( D (⟪ α ⟫↪ m) φ ≡ ⟪ Lset α ⟫↪ x )
            × ( fst (sq α α∈suc infα)
                  ( m
                  , fst (SC.Bound.formula-bound α oα infα (sq α α∈suc infα)
                           {K = ⟪ Lset (⟪ α ⟫↪ m) ⟫} (ih m)) φ )
                ≡ y ) ) ∥₁
      , squash₁ )
class-pred-is _ _ _ _ _ _ _ _ _ = refl

-- 3.5  AND THE SELECTION IS THE ORDINAL ORDER, as the predecessor said.
--      `h` (src/L/StageCardinal.lagda.md:349-351) is `leastOf` over
--      `OrdSWO.ordSWO` (:258-264), the members of α under ∈.
h-is-leastOf :
    (α : V ℓ) (α∈suc : ⟨ α ∈ˢ sucV α₀ ⟩) (oα : IsOrd α)
    (infα : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
    (D : (δ : V ℓ) → Formula ⟪ Lset δ ⟫ 1 → V ℓ)
    (inv : (δ : V ℓ) (y : V ℓ) → ⟨ y ∈ˢ 𝒟ₒ (Lset δ) ⟩
         → ∥ Σ[ φ₀ ∈ Formula ⟪ Lset δ ⟫ 1 ] (D δ φ₀ ≡ y) ∥₁)
    (ih : (m : ⟪ α ⟫) → ⟪ Lset (⟪ α ⟫↪ m) ⟫ ↪ ⟪ α ⟫)
    (x : ⟪ Lset α ⟫)
  → SC.LimitStep.h α α∈suc oα infα D inv ih x
    ≡ fst (leastOf (SC.OrdSWO.ordSWO α oα) lem
             (SC.LimitStep.class-pred α α∈suc oα infα D inv ih x)
             (SC.LimitStep.nonempty α α∈suc oα infα D inv ih x))
h-is-leastOf _ _ _ _ _ _ _ _ = refl

-- 3.6  **AND INGREDIENT (iv) IS THE CONCLUSION, ONE STAGE DOWN.**
--      TYPE ONLY, so no conversion problem is created: `[LJ-1.584]`
--      measured that `step` in one does not terminate
--      (agents/tasks/LJ-1-584/runs/w3b-1.out).
--      At the real site the fifth argument of `limit-step` is `branch`
--      (src/L/StageCardinal.lagda.md:562), and `branch`
--      (:534-537) takes the induction hypothesis of
--      `stage-card-upper`'s own ∈-induction (:564-566).
branch-at-the-site :
    (α : V ℓ) (oα : IsOrd α) (α∈suc : ⟨ α ∈ˢ sucV α₀ ⟩)
    (infα : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
  → ((δ : V ℓ) → ⟨ δ ∈ˢ α ⟩ → SC.Upper.P δ)
  → (m : ⟪ α ⟫) → ⟪ Lset (⟪ α ⟫↪ m) ⟫ ↪ ⟪ α ⟫
branch-at-the-site = SC.Upper.branch

-- AND `P` IS THE TARGET'S OWN INJECTION, so "the induction hypothesis"
-- and "the thing being built" are ONE TYPE
-- (src/L/StageCardinal.lagda.md:530-532).
P-is-the-injection :
    (δ : V ℓ) → SC.Upper.P δ
              ≡ ( IsOrd δ → ⟨ δ ∈ˢ sucV α₀ ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥)
                → (⟪ Lset δ ⟫ ↪ ⟪ δ ⟫) )
P-is-the-injection _ = refl


-- ===================================================================
-- SECTION 4.  WHAT THE TREE ALREADY HAS.
--
--   SECTION 3 SAYS ROUTE 2 NEEDS MORE THAN A PAIRING.  This section
--   says HOW MUCH more, by re-ascribing the two machines a next brief
--   would spend, so the price is not an opinion.
--
--   **THE RECURSION IS NOT THE BLOCK.**  `src/L/Recursion.lagda.md` is
--   titled "Recursive definitions are internalizable"
--   (src/L/Recursion.lagda.md:1) and its
--   condition is the graph alone: "A recursive definition is
--   internalizable when its graph is expressible, and nothing about the
--   recursion's shape, its depth, its order of descent, or the
--   complexity of its clauses appears in the condition"
--   (src/L/Recursion.lagda.md:259-261).  So ingredient (iv) costs a
--   FORMULA and not a new induction principle.
-- ===================================================================

recursion-from-a-definition : Definition → Recursion
recursion-from-a-definition = asRecursion

-- The table is an L-set BY CONSTRUCTION, not by a theorem:
-- "The table is the replacement image, so it is an element of `L` by
-- construction rather than by a theorem" (src/L/Recursion.lagda.md:153-154),
-- and the field is `Of.table` (src/L/Recursion.lagda.md:179-180).
table-of : Definition → S
table-of Dn = Of.table (asRecursion Dn)

-- 4.2  AND THE STAGE TOWER IS ALREADY AN OBJECT OF L, so ingredient
--      (iv)'s index is nameable inside the model.  `hierL`
--      (src/L/Hierarchy.lagda.md:621-622) is the internal hierarchy:
--      the L-set of the pairs of an ordinal and the tower's value there.
internal-hierarchy : (α : V ℓ) → ⟨ isL α ⟩ → IsOrd α → S
internal-hierarchy = hierL

internal-hierarchy-spec :
    (α : V ℓ) (hα : ⟨ isL α ⟩) (oα : IsOrd α)
  → IsHier α (internal-hierarchy α hα oα)
internal-hierarchy-spec = hierL-spec

-- 4.3  AND INGREDIENT (v) IS IN THE TREE TOO, WHICH I DID NOT EXPECT
--      BEFORE THE C-42 SWEEP.  `L.Coding.CodeSet` gives every META
--      formula over an AMBIENT carrier `⟪ fst A ⟫` a CODE that is an
--      L-set (src/L/Coding/CodeSet.lagda.md:300-301), and collects all
--      of them, at every arity, into ONE L-set
--      (src/L/Coding/CodeSet.lagda.md:440-443).  So the existential of
--      3.4 has an object-language range: at `A := LsetS δ oδ` the
--      carrier is `⟪ Lset δ ⟫`, which is exactly ingredient (v)'s.
coded-syntax : (A : S) {n : ℕ} → Formula ⟪ fst A ⟫ n → S
coded-syntax A = keyS A

all-codes : S → S
all-codes = AllCodes

coded-syntax-collected :
    (A : S) {n : ℕ} (φ : Formula ⟪ fst A ⟫ n)
  → ⟨ coded-syntax A φ SL.∈ˢ all-codes A ⟩
coded-syntax-collected A φ = key∈AllCodes A φ


-- ===================================================================
-- SECTION 5.  THE VERDICT.
--
--   **NO TERM NAMED `pairing-suffices` IS IN THIS FILE, AND NOTHING
--   ABOVE IS OFFERED AS ONE.**
--
--   `DefPairing` (section 2) is the weakest definable-pairing
--   hypothesis I can state.  Section 3 measures that it is ONE of FIVE
--   ingredients of `class-pred`, and that two of the other four are
--   NOT internal: `ih`, which is the target's own injection one stage
--   down (3.6), and the meta syntax `Formula ⟪ Lset δ ⟫ 1` that the
--   existential quantifier of `class-pred` ranges over (3.4 (v)).
--
--   SO `DefPairing α → Target α` IS NOT A THEOREM OF THIS TREE, and it
--   is not one line.  **THE BRIEF'S PREMISE THAT "THE MODULE IS ONE
--   SUBSTITUTION AWAY FROM CARRYING A FORMULA" IS FALSE AS MEASURED**,
--   and `agents/tasks/LJ-1-594/review-of-pairing-suffices.md` states
--   the NO-GO with the price.
--
--   **AND THE HYPOTHESIS IS NOT TOO STRONG.  IT IS TOO WEAK.**  The
--   brief asks what to say if the pairing hypothesis turns out as
--   strong as the conclusion.  IT DOES NOT.  `DefPairing` describes one
--   binary function on the members of ONE ordinal; the conclusion is an
--   injection of a whole stage.  The hypothesis is strictly weaker than
--   the conclusion and STILL NOT SUFFICIENT, which is a different
--   answer from the one the brief anticipated.
--
--   SECTION 4 IS THE HALF THAT IS GOOD NEWS, and it is why the review
--   prices route 2 rather than closing it.  EVERY ONE of the five
--   ingredients has a machine in `src/` today: (i) 3.1, (ii) 3.5,
--   (iii) the hypothesis, (iv) `src/L/Recursion.lagda.md:259-261` with
--   `src/L/Hierarchy.lagda.md:621`, (v) 4.3.  WHAT IS MISSING IS THE
--   ONE `Formula` THAT TIES THEM TOGETHER, with its `defines` and its
--   `only`.  That is a chapter of `src/`, and it is NOT the
--   substitution of a module parameter.
-- ===================================================================

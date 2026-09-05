{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.572]  `Def` FOR B9's `g`.  THE OBLIGATION IS NOT DELIVERED, AND
--             THIS FILE IS THE MEASUREMENT THAT SAYS WHY.
--
-- W3 IS agents/tasks/LJ-1-572/runs/W3.agda AND IT WAS WRITTEN FIRST AND
-- TYPECHECKED ALONE.  Exit 0, runs/w3-2.out, 421.37 s.  Its finding is
-- section 5 below.
--
-- **THE NAME `b9-g-is-definable` IS DELIBERATELY NOT BOUND ANYWHERE IN
-- THIS FILE.**  The obligation is NOT delivered.  No row below may be
-- read as it.  The stop is stated at
-- agents/tasks/LJ-1-572/review-of-b9-g-definable.md.
--
-- THIS FILE CARRIES NO HOLE AND NO POSTULATE, so every row in it is a
-- measurement and not a claim ([LJ-1.533]'s discipline, kept by
-- [LJ-1.549], [LJ-1.552], [LJ-1.554], [LJ-1.557], [LJ-1.561],
-- [LJ-1.566] and [LJ-1.568]).  Nothing lands in `src/`.
--
-- EVERY HYPOTHESIS BELOW IS A PREMISE OF THE ROW THAT NAMES IT.  The
-- point of such a row is that the tree does not supply that premise.
--
-- THE ANSWER IN ONE LINE.  THE ARITY THE BRIEF PRICED AS "the whole
-- risk" IS FREE (section 1).  WHAT STOPS THE TASK IS THAT `InjCode`
-- NAMES NO FUNCTION (section 2), THAT [LJ-1.566]'s FRAME MISSES B9 ON
-- BOTH COMPONENTS (section 3), AND THAT AN `InjCode` AT B9's PAIR **IS**
-- B9's OBLIGATION (section 4).  Section 6 closes the circle: the
-- obligation, taken as a hypothesis, PAYS ROW 4 OUTRIGHT.
--
--   Section 0.  The obligation's type, written out.  NOT inhabited.
--   Section 1.  D-10, FIRST: the arity.  It is free.
--   Section 2.  D-10, SECOND: the two directions.  `InjCode` has neither.
--   Section 3.  THE FRAME.  Two misses, two premises.
--   Section 4.  `InjCode` at B9's pair IS B9's obligation.
--   Section 5.  What B9's `g` is, and where `sq` enters.
--   Section 6.  THE CIRCLE.  The obligation is row 4 itself.
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

module LJ-1-572.Probe572 {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
  (α₀ : V ℓ) (oα₀ : IsOrd α₀)
  (sq : (δ : V ℓ) → ⟨ δ ∈ InfinitySet.sucV α₀ ⟩ → (⟨ δ ∈ InfinitySet.ω {ℓ} ⟩ → Empty.⊥)
      → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
          ((x y : ⟪ δ ⟫ × ⟪ δ ⟫) → f x ≡ f y → x ≡ y)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-induction )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; Lset; Lset→isL )
open import L.Ordinal {ℓ} using ( suc-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import L.Coding.Model {ℓ} using ( svAt; domAt )
open import L.Coding.Injection {ℓ} lem using ( injAt )
open import L.Cardinal {ℓ} lem using ( InjCode; _↪_ )
open import L.GCH {ℓ} lem using ( InjL )
import L.StageCardinal
import L.StageBound

open import Cubical.Data.FinData using ( Fin; zero; suc )
open import Cubical.Data.Sigma using ( _×_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫↪ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )
open InfinitySet {ℓ} using ( sucV; ω )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))

module SV = hPropStructure 𝒮ᵥ
module SL = hPropStructure 𝒮ʟ
open SL using ( S )

-- The delivered chapter, at this pane's parameters.  NOT rebuilt.
module SC = L.StageCardinal {ℓ} lem α₀ oα₀ sq

-- The square-law chapter, for section 5.5.  NOT rebuilt.
module SB = L.StageBound {ℓ} lem

-- THE THREE PREDECESSORS THIS FILE STANDS ON.  Each is GO and each
-- probe is green and carries no hole, so every type below is IMPORTED
-- from the file that typechecked and none is transcribed.
import LJ-1-561.Probe561 {ℓ} lem α₀ oα₀ sq as P561
import LJ-1-566.Probe566 {ℓ} lem as P566
import LJ-1-568.Probe568 {ℓ} lem α₀ oα₀ sq as P568


-- ===================================================================
-- SECTION 0.  THE OBLIGATION'S TYPE, WRITTEN OUT.  NOT INHABITED.
--
--   The brief asks for `[LJ-1.568]`'s `Def a b g` at B9's own `g`.
--   `a`, `b` and `g` are `w→B9`'s three arguments to `w→code`
--   (Probe561.agda:379-381), and `[LJ-1.568]` named all three
--   (Probe568.agda:102-103 for `ordS`, :144-147 for `B9-g`).
--
--   NOTHING BELOW INHABITS THIS TYPE.  Sections 1 to 6 say why.
-- ===================================================================

--   THE SIDE CONDITIONS ARE BOUND AND NAMED, so that the `g` is the
--   site's own `g` and not a `g` at some other pair of witnesses.
Obligation : Type (ℓ-suc ℓ)
Obligation =
    (δ : V ℓ) (oδ : IsOrd δ) (δ∈suc : ⟨ δ SV.∈ˢ sucV α₀ ⟩)
  → (infδ : ⟨ δ SV.∈ˢ ω ⟩ → Empty.⊥)
  → P568.Def (LsetS δ oδ) (P568.ordS δ oδ)
      (fst (P568.B9-g δ oδ δ∈suc infδ))


-- ===================================================================
-- SECTION 1.  D-10, BEFORE ANY OTHER AGDA.  THE ARITY.
--
--   THE BRIEF ORDERS THIS FIRST and calls it "the whole risk in this
--   task".  IT IS NOT A RISK.
--
--   `Def` wants a `Formula S 3`: `Def a b g` is
--   `P554.LinkAt a (val a b g)` (Probe568.agda:189-190) and `LinkAt`'s
--   Σ is over `Formula S 3` (Probe554.agda:81-82).
--
--   `InjCode`'s three formula conjuncts are USED at arity 2, at the
--   environment `(F ∷ a ∷ [])` (src/L/Cardinal.lagda.md:225-227).  BUT
--   THEY ARE NOT FIXED AT 2.  Each one is arity-polymorphic:
--     `svAt  : ∀ {n} → Fin n → Formula S n`   src/L/Coding/Model.lagda.md:210
--     `domAt : ∀ {n} → Fin n → Fin n → Formula S n`   :278
--     `injAt : ∀ {n} → Fin n → Formula S n`   src/L/Coding/Injection.lagda.md:44
--
--   SO THEY COME TO 3 AT NO COST.  The three rows below are that fact,
--   CHECKED.  The answer to the brief's first question is: the arity
--   can be brought to 3, and it is not what stops the task.
-- ===================================================================

svAt₃ : Formula S 3
svAt₃ = svAt zero

domAt₃ : Formula S 3
domAt₃ = domAt zero (suc zero)

injAt₃ : Formula S 3
injAt₃ = injAt zero


-- ===================================================================
-- SECTION 2.  D-10, SECOND READING.  THE TWO DIRECTIONS.
--
--   `Def a b g` has TWO halves and BOTH mention `g`
--   (Probe554.agda:83-86: one half sends a value to satisfaction, the
--   other reads a value back out of satisfaction).
--
--   `InjCode` TAKES THREE SETS AND NO FUNCTION.  So no instance of it
--   can state either half.  THE ANSWER TO THE BRIEF'S SECOND QUESTION
--   IS: NEITHER.  The row below is that arity, checked.
-- ===================================================================

injcode-names-no-function : S → S → S → Type (ℓ-suc ℓ)
injcode-names-no-function = InjCode

-- AND THE ONE BRIDGE THE TREE HAS BETWEEN A CODE AND `Def` RUNS THE
-- OTHER WAY: FROM a graph L-set TO `Def` (Probe568.agda:368-371).  A
-- graph L-set is `W`'s conclusion (Probe561.agda:160-163), not a
-- premise anything at B9 supplies.  RE-ASCRIBED, TYPE ONLY.
graph-gives-def :
    (a b : S) (g : ⟪ fst a ⟫ → ⟪ fst b ⟫)
  → Σ[ G ∈ S ] P561.IsGraph a b g G → P568.Def a b g
graph-gives-def = P568.graph→def


-- ===================================================================
-- SECTION 3.  THE FRAME.  [LJ-1.566]'s INSTANCE IS NOT AT B9's PAIR,
--             AND IT MISSES ON BOTH COMPONENTS.
--
--   THE BRIEF SAYS: "IF [LJ-1.566]'s FRAME IS NOT B9's FRAME, SAY SO
--   AND STOP."  IT IS NOT.  THIS SECTION IS THAT STOP, MEASURED.
-- ===================================================================

-- 3.1  THE DELIVERED TERM, RE-ASCRIBED.  TYPE ONLY, from the file that
--      typechecked (Probe566.agda:492-500).
p566-frame :
    (a : S) (oa : IsOrd (fst a))
  → InjCode (P566.Carve.G a oa) a (P566.Carve.C a oa)
p566-frame = P566.injcode-assembled

-- 3.2  MISS ONE, THE `a`.  `injcode-assembled` asks for `IsOrd (fst a)`,
--      because the carve runs on the ordinal well-order of `fst a`
--      (Probe566.agda:129-130).  B9's `a` is `LsetS δ oδ`, and the row
--      below identifies its carrier: it is `Lset δ`, A STAGE OF L AND
--      NOT AN ORDINAL.  With 3.1's ascribed signature this says that at
--      B9's `a` the term demands `IsOrd (Lset δ)`, and **NOTHING IN THE
--      TREE SUPPLIES THAT.**
B9-a-carrier : (δ : V ℓ) (oδ : IsOrd δ) → fst (LsetS δ oδ) ≡ Lset δ
B9-a-carrier _ _ = refl

-- 3.3  MISS TWO, THE `b`, AND IT SURVIVES ANY REPAIR OF MISS ONE.
--      `[LJ-1.566]`'s `b` is `Carve.C a oa`, the bounding ordinal the
--      carve PRODUCES out of the rank well-order
--      (Probe566.agda:132-141, :323-324).  B9's `b` is `δ`, GIVEN
--      (Probe561.agda:380).  Section 3.1's ascription carries that: the
--      `b` is an OUTPUT of the term and never an input to it, so no
--      instance of it can be steered to B9's `b`.
--
-- 3.4  AND THE MISMATCH CANNOT BE MEASURED BY APPLYING THE TERM.
--      MEASURED, and it is the sharpest number this task produced.
--      `runs/Frame.agda` is this file's sections 1 to 3 with `IsOrd (fst
--      (LsetS δ oδ))` taken as a PREMISE and `injcode-assembled` then
--      APPLIED at B9's `a`.  With every interface warm it ran past
--      300 s and was killed (`runs/frame-2.out`).  `runs/Frame2.agda`
--      is the SAME file with those two applications removed and
--      `B9-a-carrier` in their place: 1.83 s, exit 0
--      (`runs/frame2-1.out`).  A cold first attempt on the same file
--      ran 1360.52 s to a kill, exit 143, peak RSS 2.31 GB against a
--      -M8g cap and CPU time equal to elapsed, so it was a runaway
--      elaboration and NOT a heap wall (`runs/frame-1.out`).
--
--      **SO THE QUESTION "DOES [LJ-1.566]'s CARVE APPLY AT B9's `a`"
--      CANNOT BE PUT TO THE ELABORATOR AT ALL.**  The carve at a
--      non-ordinal carrier does not reduce.  That is a stronger result
--      than the mismatch: not only is the premise unsupplied, the
--      instance that would consume it does not elaborate.


-- ===================================================================
-- SECTION 4.  AND `InjCode` AT B9's PAIR **IS** B9's OBLIGATION.
--
--   THIS IS THE REASON THAT WOULD STAND EVEN IF BOTH PREMISES OF
--   SECTION 3 WERE PAID.  `InjL a b` is `∥ Σ[ F ∈ S ] InjCode F a b ∥₁`
--   (src/L/GCH.lagda.md:37-38), and B9's obligation is
--   `InjL (LsetS δ oδ) (ordS δ oδ)` (Probe561.agda:376-378).
--
--   SO A TERM OF `InjCode` AT B9's PAIR PAYS B9.  It is DOWNSTREAM of
--   the question this brief asks, not upstream of it.  The brief's
--   central premise inverts the dependency.
-- ===================================================================

B9-obligation-unfolds :
    (δ : V ℓ) (oδ : IsOrd δ)
  → InjL (LsetS δ oδ) (P568.ordS δ oδ)
  ≡ ∥ Σ[ F ∈ S ] InjCode F (LsetS δ oδ) (P568.ordS δ oδ) ∥₁
B9-obligation-unfolds _ _ = refl


-- ===================================================================
-- SECTION 5.  WHAT B9's `g` IS, AND WHERE `sq` ENTERS.
--
--   W3 (runs/W3.agda) unfolded the definition and checked every hop by
--   `refl`.  THE TWO HOPS ARE REPEATED HERE so that this file carries
--   the finding and not a pointer to it.
-- ===================================================================

-- 5.1  THE MAP, AT THE CARRIERS `w→code` NAMES.  RE-ASCRIBED, TYPE
--      ONLY, and it is [LJ-1.568]'s own row (Probe568.agda:144-147).
B9-g : (δ : V ℓ) (oδ : IsOrd δ) → ⟨ δ SV.∈ˢ sucV α₀ ⟩
     → (⟨ δ SV.∈ˢ ω ⟩ → Empty.⊥)
     → ⟪ fst (LsetS δ oδ) ⟫ ↪ ⟪ fst (P568.ordS δ oδ) ⟫
B9-g = SC.Upper.stage-card-upper

-- 5.2  HOP 1.  The map IS an ∈-recursion, and `step` is its body.
--      src/L/StageCardinal.lagda.md:564-566.
unfold-1 : SC.Upper.stage-card-upper ≡ ∈-induction SC.Upper.step
unfold-1 = refl

-- 5.3  HOP 2.  `step`'s body is `limit-step` at the branch family.
--      src/L/StageCardinal.lagda.md:561-562.
unfold-2 : (α : V ℓ) (IH : (δ : V ℓ) → ⟨ δ SV.∈ˢ α ⟩ → SC.Upper.P δ)
           (oα : IsOrd α) (α∈suc : ⟨ α SV.∈ˢ sucV α₀ ⟩)
           (infα : ⟨ α SV.∈ˢ ω ⟩ → Empty.⊥)
         → SC.Upper.step α IH oα α∈suc infα
         ≡ SC.limit-step α α∈suc oα infα (SC.Upper.branch α oα α∈suc infα IH)
unfold-2 _ _ _ _ _ = refl

-- 5.4  AND HOP 3 IS THE FINDING.  `limit-step` counts the formulas of
--      every earlier stage into `α`, and its counting bound is
--      `Bound α oα infα (sq α α∈suc infα)`
--      (src/L/StageCardinal.lagda.md:283, used at :287-292).  So every
--      value of B9's `g` is a value of `sq`.
--
--      `sq` IS A BARE MODULE PARAMETER (src/L/StageCardinal.lagda.md:17-19).
--      IT CARRIES INJECTIVITY AND NOTHING ELSE: no formula, no `isL`,
--      no stage, no grade.  Nothing in the tree gives it a formula, and
--      [LJ-1.568] recorded that sentence
--      (agents/tasks/LJ-1-568/lj-1.568-report.md:132).
--
--      **THIS ROW IS EVIDENCE AND NOT A REFUTATION.**  `Def` is not
--      proved FALSE at this `g`, and it cannot be: a definable `sq`
--      would make it true.  What is measured is that the obligation's
--      truth is a function of a parameter the module quantifies over.
sq-bare : (δ : V ℓ) → ⟨ δ SV.∈ˢ sucV α₀ ⟩ → (⟨ δ SV.∈ˢ ω ⟩ → Empty.⊥)
        → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
            ((x y : ⟪ δ ⟫ × ⟪ δ ⟫) → f x ≡ f y → x ≡ y)
sq-bare = sq

-- 5.5  AND `sq` IS NOT AN ANONYMOUS PARAMETER.  IT IS `SqFam α₀`, THE
--      SQUARE-LAW FAMILY (src/L/StageBound.lagda.md:36-40).  The row
--      below is that identity, CHECKED.
--
--      **SO THE OBSTRUCTION AT ROW 4 IS THE OBJECT OF ANOTHER OPEN ROW
--      OF THE SAME BILL.**  `SqFam`'s own producer is `SqCollect`, and
--      the chapter's own comment on the line above it says
--      "Not inhabited" (src/L/StageBound.lagda.md:42).  [LJ-1.550]
--      records the same thing at R2 (`SqAt`, Probe550.agda:304-311).
--      `[LJ-1.564]`'s bill carries `P550.SqAt` as row 2
--      (Probe564.agda:456-464).
sq-is-SqFam : SB.SqFam α₀
sq-is-SqFam = sq


-- ===================================================================
-- SECTION 6.  THE CIRCLE.  THE OBLIGATION IS ROW 4 ITSELF.
--
--   [LJ-1.568] proved "no free lunch at B9" at a QUANTIFIED `H`
--   (no-free-lunch-at-B9, Probe568.agda:454-463).  THE ROW BELOW PUTS
--   IT AT THIS BRIEF'S OWN HYPOTHESIS AND AT B9's OWN `g`, so the
--   identity is CHECKED and not quoted.
--
--   READ IT AS A PRICE.  The brief estimates the obligation at about 40
--   lines.  Hand me the obligation and I hand back
--   `InjL (LsetS δ oδ) (ordS δ oδ)`, which IS row 4 of [LJ-1.564]'s
--   bill.  **The obligation is not a step toward row 4.  It is row 4.**
-- ===================================================================

obligation-pays-B9 :
    Obligation
  → (δ : V ℓ) (oδ : IsOrd δ) (δ∈suc : ⟨ δ SV.∈ˢ sucV α₀ ⟩)
  → (infδ : ⟨ δ SV.∈ˢ ω ⟩ → Empty.⊥)
  → InjL (LsetS δ oδ) (P568.ordS δ oδ)
obligation-pays-B9 ob δ oδ δ∈suc infδ =
  P568.restrict→B9 P568.Def∥ P568.def∥-restricted δ oδ δ∈suc infδ
    ∣ ob δ oδ δ∈suc infδ ∣₁

-- AND THE ADDRESS [LJ-1.568] LEFT, RE-ASCRIBED, TYPE ONLY.  B9's
-- obligation NAMES NO FUNCTION, so ANY injection at that pair will do
-- (Probe568.agda:490-495).  The classical route uses the `<ʟ`-least
-- witness map of a DEFINABLE well-order, whose graph carries a formula
-- by construction (dev/literature/devlin-II5.md:259-270).  **THAT IS A
-- DIFFERENT `g` AND A DIFFERENT TASK.**  AD12 gives this brief one
-- obligation and I did not build it.
b9-takes-any-g :
    (H : P568.Hyp) → P568.Restrict H
  → (δ : V ℓ) (oδ : IsOrd δ)
  → Σ[ e ∈ (⟪ fst (LsetS δ oδ) ⟫ ↪ ⟪ fst (P568.ordS δ oδ) ⟫) ]
      H (LsetS δ oδ) (P568.ordS δ oδ) (fst e)
  → InjL (LsetS δ oδ) (P568.ordS δ oδ)
b9-takes-any-g = P568.B9-any-g

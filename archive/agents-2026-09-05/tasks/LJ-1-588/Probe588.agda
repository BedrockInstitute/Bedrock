{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.588]  DOES `gch-from-five` NEED ROW 4 UNRESTRICTED?
--
-- W3 IS agents/tasks/LJ-1-588/runs/W3.agda AND IT WAS WRITTEN FIRST
-- AND TYPECHECKED ALONE, as the brief ordered.  Two runs, exit 0:
-- runs/w3-1.out (COLD) and runs/w3-2.out (WARM).  Its finding is
-- section 0.1 below.
--
-- THE ANSWER IN ONE LINE.  NO.  THE BILL NEVER SPENDS ROW 4 AT A δ
-- WHERE `[LJ-1.585]`'s TWO SIDE CONDITIONS FAIL, and the obligation of
-- section 5 is `gch-from-five` with row 4 replaced by the restricted
-- row and NO NEW HYPOTHESIS on the bill.
--
-- THE ONE THING THAT MOVES, AND IT IS NOT A WIDENING.  The tower
-- parameter α₀ is QUANTIFIED, exactly as `L.StageCardinal` quantifies
-- it (src/L/StageCardinal.lagda.md:15-19).  Section 4 measures what
-- happens if it is not: a single fixed α₀ forces a hypothesis that
-- bounds EVERY infinite L-cardinal, and that row is on nobody's bill.
--
-- THIS FILE CARRIES NO HOLE AND NO POSTULATE, so every row in it is a
-- measurement and not a claim.  NOTHING LANDS IN `src/`.  Row 4 is
-- never built, the formula is never written, and `Row4RestrictedGeneric`
-- is a hypothesis from the first line to the last.
--
--   Section 0.  D-10, THE SPEND SITE.  Before any other Agda.
--   Section 1.  CONDITION ONE IS FREE, and it is the site's own term.
--   Section 2.  CONDITION TWO IS FREE once α₀ is quantified.
--   Section 3.  SO THE RESTRICTED ROW PAYS THE SPEND.
--   Section 4.  AND THE FIXED-TOWER FORM DOES NOT.  The price, named.
--   Section 5.  THE OBLIGATION.
--
-- CALIBER.  The program set GHCRTS="-A64m -I0 -M8g" on this pane.  I
-- did not set it.  One Agda process at a time.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-588.Probe588 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Model {ℓ} using ( self∈sucV )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; IsOrd; Lset; isL; isL-trans; Lset→isL )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import L.Cardinal {ℓ} lem using ( IsCardinalL )
open import L.Ordinal {ℓ} using ( ω-ord; suc-ord )
open import L.GCH {ℓ} lem using ( GCHStatement; SuccCardL; InjL )
import FOL.ZFModel
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( ω; sucV )
open import Cubical.Data.Sigma using ( _×_; Σ≡Prop )
open import Cubical.Foundations.Prelude using ( subst2 )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )

module SV = hPropStructure 𝒮ᵥ
module SL = hPropStructure 𝒮ʟ
module ModelL = FOL.ZFModel 𝒮ʟ

-- THE THREE PREDECESSORS, EACH AT THE TYPE ITS OWN REPORT DELIVERED.
-- `[LJ-1.564]` is GO (agents/tasks/LJ-1-564/lj-1.564-report.md:1),
-- `[LJ-1.585]` is GO (agents/tasks/LJ-1-585/lj-1.585-report.md:1) and
-- `[LJ-1.550]` is NO-GO on its own obligation only
-- (agents/tasks/LJ-1-550/lj-1.550-report.md:16), so `UseSite` and
-- `SqLaw` below are green terms of a green module.  Nothing is
-- transcribed.
import LJ-1-550.Probe550
import LJ-1-558.Probe558
import LJ-1-564.Probe564
import LJ-1-585.Probe585
module P550 = LJ-1-550.Probe550 {ℓ} lem
module P558 = LJ-1-558.Probe558 {ℓ} lem
module P564 = LJ-1-564.Probe564 {ℓ} lem

-- `[LJ-1.585]` IS A MODULE OVER THE TOWER, so it is aliased over the
-- tower and not at one α₀.  THIS IS THE WHOLE MOVE OF THIS FILE and it
-- is not a widening: `L.StageCardinal` takes α₀, oα₀ and sq as
-- parameters (src/L/StageCardinal.lagda.md:15-19), so
-- `stage-card-upper` EXISTS at every α₀, and a hypothesis about it may
-- be stated at every α₀ without being stated more widely than the
-- function.
--
-- `P550.SqLaw α₀` (Probe550.agda:82-87) IS `L.StageCardinal`'s own `sq`
-- slot, and this line is the elaborator saying so: if the two types
-- differed by one implicit the module application would not check.
module P585 (α₀ : V ℓ) (oα₀ : IsOrd α₀) (sq : P550.SqLaw α₀) =
  LJ-1-585.Probe585 {ℓ} lem α₀ oα₀ sq

-- An ordinal as an L-element.  RE-TYPED AND NOT IMPORTED, for the
-- reason `[LJ-1.561]` gives for re-typing it (Probe561.agda:106-108):
-- the only module that exports it is `[LJ-1.568]`'s `ordS`
-- (Probe568.agda:103-104), and that module takes the tower parameters,
-- so at a QUANTIFIED α₀ there is no name for it.  Row 2.2 below is the
-- `refl` that says this copy is the same object.
isL-ord : (β : V ℓ) → IsOrd β → ⟨ isL β ⟩
isL-ord β oβ = Lset→isL (sucV β) (suc-ord oβ) β (ord∈Lset-suc β oβ)

ordS : (β : V ℓ) → IsOrd β → SL.S
ordS β oβ = β , isL-ord β oβ


-- ===================================================================
-- SECTION 0.  D-10, THE SPEND SITE, BEFORE ANY OTHER AGDA.
--
--   THE BRIEF ORDERS THIS FIRST AND AT `file:line`: every place row 4
--   is applied, and with what δ.
--
--   0.0  THE COUNT, BY GREP.  `b9` occurs TWELVE times in
--        `agents/tasks/LJ-1-564/Probe564.agda`, one to a line: :209,
--        :210, :234, :235, :358, :359, :376, :378, :416, :417, :462,
--        :463.  It is APPLIED at EXACTLY ONE of them, `:210`,
--        `b9 δ Lδ ordδ refl`.  The other eleven are binders (:209,
--        :234, :358, :376, :416, :462) or pass-throughs (:235, :359,
--        :378, :417, :463).  SO THERE IS ONE SPEND SITE.
--
--   0.1  W3's FINDING, AND IT IS ABOUT WHAT IS IN SCOPE THERE.  The
--        spend lives in `power-into-succ-from-landing`
--        (Probe564.agda:203-226), whose own head carries NEITHER
--        `IsOrd (fst κ)` NOR `κ ∉ ω`.  BUT `gch-from-five` DOES NOT
--        REACH IT THROUGH THAT HEAD.  It reaches it through
--        `power-into-succ-at` (Probe564.agda:351-360), whose type is
--        `PowerIntoSuccAt` (Probe564.agda:327-330), and that type binds
--        BOTH.  The chain is `gch-from-five` (:462-463) →
--        `gch-from-here-sharp` (:416-417) → `gch-from-here` (:376-378)
--        → `power-into-succ-at` (:358-359).  `power-into-succ`
--        (:232-235) is the OTHER caller and it is not on this chain.
--
--   0.2  AND WITH WHAT δ.  The δ is bound by `SuccCardL δ κ`
--        (src/L/GCH.lagda.md:46-53), produced by `[LJ-1.528]`'s
--        `b4-paid` (Probe564.agda:439-440) inside
--        `gch-route-with-premised-hard` (Probe564.agda:335-341).  It is
--        THE SUCCESSOR CARDINAL OF κ IN L, and its third conjunct
--        `⟨ fst κ ∈ fst δ ⟩` (src/L/GCH.lagda.md:50) is the only thing
--        that ties it to κ.
-- ===================================================================

-- W3's `Row4Spend`, re-ascribed here.  This is `b9 δ Lδ ordδ refl`'s
-- type at Probe564.agda:210, with `Lδ` inlined from :222-223 and with
-- everything `power-into-succ-at` has in scope written out.
Row4Spend : Type (ℓ-suc ℓ)
Row4Spend =
    (κ δ : SL.S) → IsOrd (fst κ) → (⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)
  → (sc : SuccCardL δ κ)
  → InjL (Lset (fst δ) , P564.stage-is-L δ (fst sc)) δ

-- 0.3  AND THE `Lδ` OF THE SPEND SITE IS `LsetS` ON THE NOSE.
--      `stage-is-L δ oδ` is `isL-Lset (fst δ) oδ` (Probe564.agda:155-156)
--      and `LsetS β oβ` is `Lset β , isL-Lset β oβ`
--      (src/L/Axioms/Basic.lagda.md:160-161).  So the source of the
--      spend and the source of `[LJ-1.585]`'s restricted row are the
--      SAME TERM, with no transport between them.  `refl` says it.
Lδ-is-LsetS : (δ : SL.S) (oδ : IsOrd (fst δ))
            → (Lset (fst δ) , P564.stage-is-L δ oδ) ≡ LsetS (fst δ) oδ
Lδ-is-LsetS δ oδ = refl


-- ===================================================================
-- SECTION 1.  CONDITION ONE IS FREE, AND IT IS THE SITE'S OWN TERM.
--
--   `[LJ-1.585]`'s first side condition is `δ ∉ ω`
--   (Probe585.agda:163-166, from src/L/StageCardinal.lagda.md:564-566).
--   THE BRIEF ASKS WHETHER `GCHStatement`'s FOURTH HYPOTHESIS
--   (src/L/GCH.lagda.md:64) PROPAGATES TO THE δ.  IT DOES, and the
--   proof is two lines that ALREADY STAND IN THE TREE at this very
--   site: `P550.UseSite.δ∉ω` (Probe550.agda:250-251).
-- ===================================================================

-- ω is transitive (src/L/Ordinal.lagda.md:263-264) and `SuccCardL`'s
-- third conjunct puts κ in δ (src/L/GCH.lagda.md:50).  So a finite δ
-- would make κ finite.
delta-not-omega :
    (κ δ : SL.S) → (⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥) → SuccCardL δ κ
  → ⟨ fst δ ∈ˢ ω ⟩ → Empty.⊥
delta-not-omega κ δ κ∉ω sc δ∈ω = κ∉ω (fst ω-ord (fst (snd (snd sc))) δ∈ω)

-- 1.1  AND IT IS NOT MY TERM.  It is the one the use site already
--      computes, lifted off `UseSite`'s telescope so the bill's other
--      four inputs are not needed to state it.  `refl` is the check
--      that nothing was changed in the lifting.
delta-not-omega-is-the-sites-own :
    (zf : ModelL.isZFModel)
    (bst : P550.BoundedSubsetTheorem) (b6 : P550.SubsetIntoStage zf)
    (b7 : P550.AbsorbsAt) (b8 : P550.LimitAbove)
    (κ δ : SL.S) (ordκ : IsOrd (fst κ)) (κ∉ω : ⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)
    (sc : SuccCardL δ κ)
  → P550.UseSite.δ∉ω zf bst b6 b7 b8 κ δ ordκ κ∉ω sc
      ≡ delta-not-omega κ δ κ∉ω sc
delta-not-omega-is-the-sites-own _ _ _ _ _ _ _ _ _ _ = refl


-- ===================================================================
-- SECTION 2.  CONDITION TWO IS FREE ONCE THE TOWER IS QUANTIFIED.
--
--   `[LJ-1.585]`'s second side condition is `δ ∈ sucV α₀`
--   (Probe585.agda:163-166), and THE BRIEF ASKS WHERE α₀ COMES FROM AT
--   THE SPEND SITE.  IT COMES FROM NOWHERE: `gch-from-five`
--   (Probe564.agda:456-463) has no α₀, and `Probe564.agda` never
--   imports `L.StageCardinal` at all.
--
--   SO THE SITE DOES NOT PICK α₀.  THE HYPOTHESIS DOES, and the
--   hypothesis may pick it at every value, because that is how the
--   function itself is stated.  Under that reading the condition is
--   free at α₀ := δ, by one line of `src/`.
-- ===================================================================

-- `[LJ-1.585]`'s `Row4Restricted` (Probe585.agda:163-166) with the
-- tower quantified.  NOT A NEW STATEMENT: the body IS that type, and
-- the three binders are `L.StageCardinal`'s own three
-- (src/L/StageCardinal.lagda.md:15-19).
Row4RestrictedGeneric : Type (ℓ-suc ℓ)
Row4RestrictedGeneric =
    (α₀ : V ℓ) (oα₀ : IsOrd α₀) (sq : P550.SqLaw α₀)
    (d : V ℓ) (od : IsOrd d) → ⟨ d ∈ˢ sucV α₀ ⟩ → (⟨ d ∈ˢ ω ⟩ → Empty.⊥)
  → InjL (LsetS d od) (ordS d od)

-- 2.0  AND THE BODY IS `[LJ-1.585]`'s ROW AND NOT A NEIGHBOUR OF IT.
--      `InjCode` is a conjunction of satisfaction facts
--      (src/L/Cardinal.lagda.md:223-228), so `InjL` is NOT injective
--      for unification and the two endpoints must be written rather
--      than inferred.  This row is the price of writing them: `refl`
--      checks that the written form IS `Row4Restricted`
--      (Probe585.agda:163-166), at every tower.
generic-is-585s :
    (α₀ : V ℓ) (oα₀ : IsOrd α₀) (sq : P550.SqLaw α₀)
  → ((d : V ℓ) (od : IsOrd d) → ⟨ d ∈ˢ sucV α₀ ⟩ → (⟨ d ∈ˢ ω ⟩ → Empty.⊥)
      → InjL (LsetS d od) (ordS d od))
    ≡ P585.Row4Restricted α₀ oα₀ sq
generic-is-585s α₀ oα₀ sq = refl

-- 2.1  TWO TRANSPORTS, EACH ACROSS AN hProp.  `SL.S` is a Σ over `isL`
--      and `isL` is an hProp (src/L/Constructible.lagda.md), so a pair
--      that agrees on the carrier is the same L-element.  These are the
--      two `Σ≡Prop`s `[LJ-1.585]` writes at Probe585.agda:199-205,
--      taken at the CARRIERS so neither endpoint has to be named: the
--      source and the target of the restricted row mention
--      `[LJ-1.568]`'s `ordS` (Probe568.agda:103-104), which no module
--      re-exports at a quantified α₀.
injL-recarry : (a b c d : SL.S)
             → fst a ≡ fst c → fst b ≡ fst d → InjL a b → InjL c d
injL-recarry a b c d ea eb =
  subst2 InjL
    (Σ≡Prop {A = SV.S} {B = λ w → ⟨ isL w ⟩} (λ w → snd (isL w)) {u = a} {v = c} ea)
    (Σ≡Prop {A = SV.S} {B = λ w → ⟨ isL w ⟩} (λ w → snd (isL w)) {u = b} {v = d} eb)

-- 2.2  ROW 4, RESTRICTED TO THE INFINITE δ, AND NOT RESTRICTED FURTHER.
--      This is the whole content of section 2: quantifying α₀ collapses
--      `[LJ-1.585]`'s TWO side conditions to ONE.  `δ ∈ sucV α₀` is
--      discharged at α₀ := fst δ by `self∈sucV`
--      (src/V/Model.lagda.md:236-237), and the square law that α₀
--      demands is `P550.SqAt` at δ, which is ROW 2 OF THE BILL and not
--      a new hypothesis (Probe550.agda:309-310, Probe564.agda:458).
Row4Infinite : Type (ℓ-suc ℓ)
Row4Infinite =
    (δ Lδ : SL.S) → IsOrd (fst δ) → (fst Lδ ≡ Lset (fst δ))
  → (⟨ fst δ ∈ˢ ω ⟩ → Empty.⊥)
  → InjL Lδ δ

generic→row4-infinite : Row4RestrictedGeneric → P550.SqAt → Row4Infinite
generic→row4-infinite r sqa δ Lδ oδ e infδ =
  injL-recarry (LsetS (fst δ) oδ) (ordS (fst δ) oδ) Lδ δ (sym e) refl
    (r (fst δ) oδ (sqa δ oδ) (fst δ) oδ (self∈sucV (fst δ)) infδ)

-- 2.3  AND `Row4Infinite` IS STRICTLY WEAKER THAN ROW 4, which is why
--      this is not a rederivation of `[LJ-1.585]`'s refuted direction.
--      Row 4 in full gives it by dropping the condition;
--      `restricted+conditions→full` (Probe585.agda:194-205) is the
--      other direction and its supply is FALSE at δ := 0
--      (`side-conditions-are-false`, Probe585.agda:219-226).  THIS FILE
--      NEVER ASKS FOR THAT DIRECTION.
full→row4-infinite : P564.StageCountedCoded → Row4Infinite
full→row4-infinite b9 δ Lδ oδ e _ = b9 δ Lδ oδ e


-- ===================================================================
-- SECTION 3.  SO THE RESTRICTED ROW PAYS THE SPEND.
--
--   Section 1 gives the surviving condition at the spend site and
--   section 2 gives the row under that condition.  Nothing else is
--   needed, and NO HYPOTHESIS BEYOND THE BILL'S OWN ROW 2 IS USED.
-- ===================================================================

restricted-at-spend : Row4RestrictedGeneric → P550.SqAt → Row4Spend
restricted-at-spend r sqa κ δ ordκ κ∉ω sc =
  generic→row4-infinite r sqa δ (Lset (fst δ) , P564.stage-is-L δ (fst sc))
    (fst sc) refl (delta-not-omega κ δ κ∉ω sc)

-- 3.1  AND ROW 4 IN FULL STILL PAYS IT, so section 5's route is a
--      WEAKENING of `[LJ-1.564]`'s and not a different route.
full-at-spend : P564.StageCountedCoded → Row4Spend
full-at-spend b9 κ δ ordκ κ∉ω sc =
  full→row4-infinite b9 δ (Lset (fst δ) , P564.stage-is-L δ (fst sc))
    (fst sc) refl (delta-not-omega κ δ κ∉ω sc)

-- 3.2  AND THE FULL ROW GIVES THE GENERIC RESTRICTED ROW AT EVERY
--      TOWER.  `[LJ-1.585]`'s `full→restricted` (Probe585.agda:188-189),
--      IMPORTED, with the tower quantified.  So `Row4RestrictedGeneric`
--      is a CONSEQUENCE of row 4 and the swap of section 5 can only
--      weaken the bill.
full→generic : P564.StageCountedCoded → Row4RestrictedGeneric
full→generic b9 α₀ oα₀ sq = P585.full→restricted α₀ oα₀ sq b9


-- ===================================================================
-- SECTION 4.  AND THE FIXED-TOWER FORM DOES NOT.  THE PRICE, NAMED.
--
--   THE BRIEF ORDERS THIS: "Say where α₀ comes from at the spend site
--   and whether the bound holds there.  If it does not, that is the
--   answer and this task is a NO-GO with a named site."
--
--   IT DOES NOT COME FROM ANYWHERE, so there is no bound to check.
--   What section 3 does instead is let the HYPOTHESIS choose α₀ at
--   each δ.  This section measures what the other reading costs, so
--   the choice is priced and not assumed.
-- ===================================================================

-- What a SINGLE fixed tower would have to be given: every successor
-- cardinal of every infinite L-cardinal, inside `sucV α₀`.
BoundAtSucc : V ℓ → Type (ℓ-suc ℓ)
BoundAtSucc α₀ = (κ δ : SL.S) → SuccCardL δ κ → ⟨ fst δ ∈ˢ sucV α₀ ⟩

-- 4.1  WITH IT, THE FIXED FORM PAYS THE SPEND TOO.  So the bound is
--      the WHOLE difference between the two readings, and nothing else
--      is hiding in section 3.
fixed-tower-with-the-bound :
    (α₀ : V ℓ) (oα₀ : IsOrd α₀) (sq : P550.SqLaw α₀)
  → P585.Row4Restricted α₀ oα₀ sq → BoundAtSucc α₀ → Row4Spend
fixed-tower-with-the-bound α₀ oα₀ sq r bd κ δ ordκ κ∉ω sc =
  injL-recarry (LsetS (fst δ) ordδ) (ordS (fst δ) ordδ)
               (Lset (fst δ) , P564.stage-is-L δ ordδ) δ refl refl
    (r (fst δ) ordδ (bd κ δ sc) (delta-not-omega κ δ κ∉ω sc))
  where
  ordδ : IsOrd (fst δ)
  ordδ = fst sc

-- 4.2  AND THE BOUND IS NOT A SMALL ROW.  IT BOUNDS EVERY INFINITE
--      L-CARDINAL.  `[LJ-1.528]`'s `SuccCardExists` is PAID
--      (Probe564.agda:439-440), so this needs no hypothesis at all
--      beyond the bound itself: every infinite L-cardinal κ has a
--      successor δ, the bound puts δ in `sucV α₀`, and `sucV α₀` is
--      an ordinal (src/L/Ordinal.lagda.md, `suc-ord`) hence transitive,
--      so κ lands there too.
--
--      THIS IS THE ROW THE CAMPAIGN WOULD HAVE TO PAY under the fixed
--      reading, and it is on nobody's bill: `gch-from-five`'s five rows
--      (Probe564.agda:456-461) contain nothing about a single tower
--      that bounds L's cardinals.  `GCHStatement` quantifies over EVERY
--      infinite L-cardinal (src/L/GCH.lagda.md:60-64).
bound-bounds-every-cardinal :
    (α₀ : V ℓ) (oα₀ : IsOrd α₀) → BoundAtSucc α₀
  → (κ : SL.S) → IsOrd (fst κ) → IsCardinalL κ
  → (⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)
  → ⟨ fst κ ∈ˢ sucV α₀ ⟩
bound-bounds-every-cardinal α₀ oα₀ bd κ ordκ cardκ κ∉ω =
  PT.rec (snd (fst κ ∈ˢ sucV α₀)) step (P564.b4-paid κ ordκ cardκ κ∉ω)
  where
  step : Σ[ δ ∈ SL.S ] SuccCardL δ κ → ⟨ fst κ ∈ˢ sucV α₀ ⟩
  step (δ , sc) = fst (suc-ord oα₀) (fst (snd (snd sc))) (bd κ δ sc)


-- ===================================================================
-- SECTION 5.  THE OBLIGATION.
--
--   `gch-from-restricted-row4` is `gch-from-five`
--   (Probe564.agda:456-463) with row 4 replaced by
--   `Row4RestrictedGeneric` AND WITH NO OTHER CHANGE.  Rows 1, 2, 3
--   and 5 are `[LJ-1.550]`'s and `[LJ-1.558]`'s own types, taken from
--   those modules and not transcribed.
--
--   THE ROUTE IS `[LJ-1.564]`'s, RE-DERIVED ONLY WHERE IT TOUCHES b9.
--   `power-into-succ-at` (Probe564.agda:351-360) takes row 4 as an
--   argument, so a substitute cannot be plugged into it; the three
--   lines below are that function with `spend` in b9's place and
--   nothing else moved.  Everything above and below it in the chain is
--   `[LJ-1.564]`'s own term, applied.
-- ===================================================================

-- Probe564.agda:203-226 with the spend in b9's place.
power-into-succ-from-spend :
    (zf : ModelL.isZFModel) → Row4Spend
  → (κ δ : SL.S) → IsOrd (fst κ) → (⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)
  → (sc : SuccCardL δ κ)
  → ((y : SL.S) → ⟨ fst y ∈ˢ fst (ModelL.isZFModel.𝒫 zf κ) ⟩
                → ⟨ fst y ∈ˢ Lset (fst δ) ⟩)
  → InjL (ModelL.isZFModel.𝒫 zf κ) δ
power-into-succ-from-spend zf spend κ δ ordκ κ∉ω sc land =
  P564.injl-trans (𝒫 κ) Lδ δ (P564.inclusion-coded (𝒫 κ) Lδ into)
                  (spend κ δ ordκ κ∉ω sc)
  where
  open ModelL.isZFModel zf using ( 𝒫 )

  ordδ : IsOrd (fst δ)
  ordδ = fst sc

  Lδ : SL.S
  Lδ = Lset (fst δ) , P564.stage-is-L δ ordδ

  into : (z : SV.S) → ⟨ z ∈ˢ fst (𝒫 κ) ⟩ → ⟨ z ∈ˢ fst Lδ ⟩
  into z z∈ = land (z , isL-trans z∈ (snd (𝒫 κ))) z∈

-- Probe564.agda:351-360 with the spend in b9's place.
power-into-succ-at-restricted :
    (zf : ModelL.isZFModel)
  → P550.BoundedSubsetTheorem → P550.SubsetIntoStage zf
  → P550.AbsorbsAt → P550.LimitAbove
  → P550.AmbientCardAtSucc → P550.SqAt → P550.CoHyps
  → Row4Spend
  → P564.PowerIntoSuccAt zf
power-into-succ-at-restricted zf bst b6 b7 b8 r1 r2 r3 spend κ ordκ κ∉ω δ sc =
  power-into-succ-from-spend zf spend κ δ ordκ κ∉ω sc
    (U.member-in-stage (r1 κ δ sc) (r2 κ ordκ) r3)
  where
  module U = P550.UseSite zf bst b6 b7 b8 κ δ ordκ κ∉ω sc

-- THE OBLIGATION.  Five rows, and the fourth is the restricted one.
gch-from-restricted-row4 :
    (zf : ModelL.isZFModel)
  → P550.AmbientCardAtSucc → P550.SqAt → P550.CoHyps
  → Row4RestrictedGeneric
  → P558.SuccIntoPower zf
  → GCHStatement zf
gch-from-restricted-row4 zf r1 r2 r3 r4 b10 =
  P564.gch-route-with-premised-hard zf P564.b4-paid
    (power-into-succ-at-restricted zf P564.bounded-subset-theorem
       (P564.b6-paid zf) P564.b7-paid P564.b8-paid r1 r2 r3
       (restricted-at-spend r4 r2))
    b10

-- 5.1  AND NOTHING WAS LOST.  `gch-from-five`'s OWN TYPE, closed
--      THROUGH THIS FILE's route: row 4 in full gives the restricted
--      row (section 3.2) and the route takes it from there.  A
--      mismatch of one implicit anywhere in the chain would be exit 42.
gch-from-five-through-the-restricted-row :
    (zf : ModelL.isZFModel)
  → P550.AmbientCardAtSucc → P550.SqAt → P550.CoHyps
  → P564.StageCountedCoded
  → P558.SuccIntoPower zf
  → GCHStatement zf
gch-from-five-through-the-restricted-row zf r1 r2 r3 b9 b10 =
  gch-from-restricted-row4 zf r1 r2 r3 (full→generic b9) b10

-- 5.2  AND IT IS `[LJ-1.564]`'s ROW AND NOT A NEIGHBOUR.  This is
--      `gch-from-five`'s type (Probe564.agda:456-461), letter for
--      letter, filled by 5.1.
five-row-bill-unchanged :
    (zf : ModelL.isZFModel)
  → P550.AmbientCardAtSucc → P550.SqAt → P550.CoHyps
  → P564.StageCountedCoded
  → P558.SuccIntoPower zf
  → GCHStatement zf
five-row-bill-unchanged = P564.gch-from-five

-- 5.3  THE HONEST BOUNDARY, AND I STATE IT BECAUSE THE BRIEF ORDERS
--      ME NOT TO READ A DISCHARGE INTO ANYTHING I DID NOT INHABIT.
--
--      NOTHING HERE PAYS ROW 4.  `Row4RestrictedGeneric` is a
--      hypothesis in every row above, and this file builds no formula
--      and no injection.  What is measured is that the BILL never asks
--      row 4 outside the restricted row's reach.
--
--      AND `[LJ-1.585]`'s REFUTATION STANDS UNTOUCHED.
--      `side-conditions-are-false` (Probe585.agda:219-226) says the
--      restricted row cannot be widened to row 4, because δ := 0 is in
--      ω.  THIS FILE AGREES AND NEVER TRIES: the only δ it spends at is
--      a successor cardinal above an infinite κ, and section 1 proves
--      that δ is not in ω.  The two statements are about different δ.

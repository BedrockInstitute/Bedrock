{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.583]  The sealed projections [LJ-1.576] could not answer.
--
-- SECTION 1 is W3.  The brief says its value is a LIST and not a type,
--   so the list is written here, each entry at file:line, and the two
--   module applications it points at were typechecked ALONE FIRST at
--   agents/tasks/LJ-1-583/runs/W3.agda (exit 0, runs/w3-1.out).
-- SECTION 2 closes GAP A and pays the row's non-emptiness with it.
-- SECTION 3 closes GAP C and pays two of kappa-min's three call sites.
-- SECTION 4 is GAP B.  IT DOES NOT CLOSE.  What IS proved here is that
--   the gap is not where [LJ-1.576] put it.
-- SECTION 5 is THE OBLIGATION.
-- SECTION 6 writes down what is NOT here.
--
-- Nothing is postulated.  Nothing lands in src/.  No hole.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-583.Probe583 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; IsOrd; isL; Lset; Lset→isL )
open import L.Stage {ℓ} lem using ( stage; stage-ord; stage-mem )
open import L.Cardinal {ℓ} lem
  using ( _↪_; InjCode; module LeastCardInjL; module SiteBound )
open import L.GCH {ℓ} lem using ( InjL )
open import L.CantorBernstein {ℓ} lem using ( readL )
open import L.InjChain {ℓ} lem using ( module InclGraph; module Comp )
open import L.CodedShift {ℓ} lem using ( shift-coded )
open import L.Axioms.Infinity {ℓ} lem using ( ωʟ )
open import L.Axioms.Numerals {ℓ} using ( sucʟ )
open import L.Choice.Step {ℓ} lem using ( Mem; orderAt )
open import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ}
  using ( SWO; IsLeast; leastOf )

-- [LJ-1.576]'s OWN TERMS.  The brief says "DO NOT REBUILD WHAT
-- [LJ-1.576] ANSWERED.  Import its terms."  This line is that order
-- obeyed: every type below that carries a superscript c, and the
-- reduction `id-coded→nonempty`, is its file's and not a copy.
open import LJ-1-576.Probe576 {ℓ} lem
  using ( isPropInjCode; IdCoded; id-coded→nonempty; CodedComp
        ; CodeBounded; AmbientCoded; CodeUnique
        ; module Coded; module CodeSelect )

open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( sucV; #_ )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )
open hPropStructure 𝒮ʟ using ( S )

-- =====================================================================
-- SECTION 1.  W3.  THE GAP LIST, READ BEFORE ANY AGDA.
--
--   The brief orders D-10 first: read agents/tasks/LJ-1-576/Probe576.agda
--   :327-382 and say which of the five sealed projections are TERMS and
--   which are NAMED GAPS.  Here is that read, and the count.
--
--   ALL FIVE ARE TERMS.  NONE OF THE FIVE IS A HOLE.
--
--     projection 1  `κ₁`  Probe576.agda:333-334   term, unconditional
--     projection 2  `κ₂`  Probe576.agda:339-341   term, unconditional
--     projection 3  `κ₃`  Probe576.agda:344-345   term, unconditional
--     projection 4  `κ₄`  Probe576.agda:353-354   term, UNDER A HYPOTHESIS
--     projection 5  `κ₅`  Probe576.agda:360-378   term, AT A WEAKER TYPE
--
--   SO THE GAPS ARE NOT HOLES IN THE FIVE.  THEY ARE THREE NAMED TYPES
--   STANDING BETWEEN THE FIVE AND THE SEAL, AND THE COUNT IS THREE.
--
--     GAP A  the module hypothesis `ne : Coded.Nonemptyᶜ α oα`, which
--            gates ALL FIVE.  Probe576.agda:327 is the binder; the
--            reduction to `IdCoded` is Probe576.agda:421-431.
--     GAP B  projection 4's antecedent `CodeSelect.BoundedCode α κ₁`.
--            Probe576.agda:353; the type is Probe576.agda:239-240.
--     GAP C  what projection 5's WEAKENING costs its three call sites,
--            `CodedComp`.  Probe576.agda:394-395; the sites are
--            src/L/SquareLawClosed.lagda.md:109, :141 and :156.
--
--   `CodeUnique` (Probe576.agda:90-91) and `AmbientCoded` (:282-283) are
--   NOT in this list.  The first is not expected to hold and gates
--   nothing; the second gates section 4's EQUALITY of the two selections
--   and not any of the five.  Both are imported above so that this file
--   names them and does not silently drop them.
--
--   MEASURED RESULT OF THIS TASK: GAP A CLOSES, GAP C CLOSES, GAP B
--   DOES NOT.  Sections 2, 3 and 4, in that order.
-- =====================================================================

-- =====================================================================
-- SECTION 2.  GAP A CLOSES, AND [LJ-1.576] MEASURED THE WRONG `Carve`.
--
--   Its report reads: "`Carve` is hardwired to the shift formula
--   `shiftFo` (src/L/Absorption.lagda.md:386, and its carve reads
--   `sep bnd (shiftFo D γ ω z)` at :413), so it does not serve."
--   THAT SENTENCE IS TRUE OF `L.Absorption.Carve` AND OF NO OTHER
--   MODULE.  THE TREE HAS TWO MODULES CALLED `Carve`.
--
--     src/L/Absorption.lagda.md:386   Carve, over `shiftFo`      (:413)
--     src/L/InjChain.lagda.md:468     Carve, over `inclFo`       (:480)
--
--   and `inclFo D = ∃̇∈ (con D) (prAtL (suc zero) zero zero)`
--   (src/L/InjChain.lagda.md:446) IS the identity graph's formula.  Its
--   own comment says so: "an inclusion IS the identity on its domain"
--   (:439).  The L instantiation is `InclGraph` (:575-598), which
--   supplies the stage bound and `hasSeparationL` and nothing else.
--
--   So the identity code is not a set to be carved by this task.  It is
--   in `src/` already, at the inclusion of a set into ITSELF, and the
--   subset witness that row spends is the identity function.
-- =====================================================================

idCoded : IdCoded
idCoded a = ∣ IG.G , (IG.sv , IG.dm , IG.ij , IG.ran) ∣₁
  where
  module IG = InclGraph a a (λ _ z∈a → z∈a)

-- AND THE ROW-LEVEL PAYOFF, WHICH IS THE POINT OF GAP A.  [LJ-1.576]
-- wrote the reduction and did not inhabit its antecedent
-- (Probe576.agda:424-431).  The antecedent is now a term, so the
-- conclusion is one: `module Five`'s hypothesis is discharged AT EVERY
-- α, and projections 1, 2, 3 and 5 lose their `ne`.
nonemptyᶜ : (α : S) (oα : IsOrd (fst α)) → Coded.Nonemptyᶜ α oα
nonemptyᶜ = id-coded→nonempty idCoded

-- The four projections that were gated by `ne` alone, now unconditional.
-- Each is [LJ-1.576]'s own term at the discharged hypothesis, NOT a
-- second proof: Probe576.agda:333-345 and :360-378.
module FiveAt (α : S) (oα : IsOrd (fst α)) where

  open Coded α oα using ( κᶜ; κ-minᶜ )

  ne : Coded.Nonemptyᶜ α oα
  ne = nonemptyᶜ α oα

  -- projection 1, unconditional
  κ₁ : S
  κ₁ = κᶜ ne

  -- projection 5, unconditional, still at the CODED refutand
  κ₅ : (b : ⟪ sucV (fst α) ⟫) → InjL α (LeastCardInjL.up α oα b)
     → SWO._<∙_ (LeastCardInjL.w α oα) b (Coded.γᶜ α oα ne) → Empty.⊥
  κ₅ = κ-minᶜ ne

-- =====================================================================
-- SECTION 3.  GAP C CLOSES, AND `comp-inj` WAS THE WRONG GREP.
--
--   [LJ-1.576] measured: "the tree has no such term.  `grep -rn
--   "comp-inj :" src/` returns THREE definitions ... and every one of
--   the three is at the AMBIENT `_↪_`."  THE GREP IS RIGHT AND THE
--   CONCLUSION IS TOO NARROW.  The coded composite is not called
--   `comp-inj`.  It is `L.InjChain.Comp` (src/L/InjChain.lagda.md:314),
--   ROW 1 of that master, "The composition of two injection graphs, by
--   separation" (:188).  It takes the FOUR CONJUNCTS of each factor and
--   returns the four conjuncts of the composite at `γK = K ∷ D ∷ []`
--   (:377-422).  That tuple IS `InjCode K a c`.
-- =====================================================================

codedComp : CodedComp
codedComp a b c =
  PT.rec (isPropΠ (λ _ → squash₁))
    (λ { (F , svF , dmF , ijF , ranF) →
      PT.map (λ { (H , svH , dmH , ijH , ranH) →
        let module K = Comp a b c F H svF dmF ijF ranF svH dmH ijH ranH
        in K.K , (K.svK , K.dmK , K.ijK , K.ranK) }) })

-- AND THE SECOND FACTOR AT TWO OF THE THREE CALL SITES, WHICH
-- [LJ-1.576] ALREADY APPLIED (Probe576.agda:409-413).  It is repeated
-- here at the composite's own type, so that the two sites are CLOSED
-- objects and not two citations.  src/L/SquareLawClosed.lagda.md:141
-- and :156 both compose with the shift.
coded-shift-comp :
    (α γ : S) (oγ : IsOrd (fst γ)) (γ∉ω : ⟨ fst γ ∈ fst ωʟ ⟩ → Empty.⊥)
    (numerals : (k : ℕ) → ⟨ # k ∈ fst γ ⟩)
  → InjL α (sucʟ γ) → InjL α γ
coded-shift-comp α γ oγ γ∉ω numerals h =
  codedComp α (sucʟ γ) γ h (shift-coded γ oγ γ∉ω numerals)

-- THE THIRD SITE, src/L/SquareLawClosed.lagda.md:109, IS NOT CLOSED
-- HERE AND [LJ-1.576] SAID WHY: its second factor is built from the
-- SQUARE (src/L/SquareLawClosed.lagda.md:111-112) and that is a
-- different object.  `codedComp` is generic in the middle set, so the
-- site needs one coded factor and no new composition law.  This type is
-- the exact remaining ask, and it is NOT inhabited here.
SquareCoded : Type (ℓ-suc ℓ)
SquareCoded = (κ β : S) → ⟪ fst κ ⟫ ↪ ⟪ fst β ⟫ → InjL κ β

-- =====================================================================
-- SECTION 4.  GAP B DOES NOT CLOSE, AND THE GAP IS NOT WHERE
-- [LJ-1.576] PUT IT.
--
--   `CodeBounded` (Probe576.agda:239-240) reads
--
--     (a b : S) → InjL a b → CodeSelect.BoundedCode a b
--
--   and `CodeSelect a b` opens `SiteBound a` (Probe576.agda:203).  SO
--   THE STAGE β IS A FUNCTION OF `a` ALONE: `SiteBound.β = stageBound
--   (fst a) (snd a) .fst` (src/L/Cardinal.lagda.md:165-166), and
--   `stageBound a p = bound2 ω (stage a p) ...`
--   (src/L/Choice/Stage.lagda.md:366-368), where `bound2` returns an
--   ordinal ABOVE its two arguments and says nothing else about it
--   (src/L/Ordinal.lagda.md:185-196).
--
--   A CODE OF AN INJECTION `a ↪ b` IS A SET OF PAIRS DRAWN FROM `a` AND
--   `b`.  Its stage therefore reads `b`.  `src/` measures exactly that
--   at the place that builds such a bound: `PairBound D C` indexes on
--   `Ix = ⟪ fst D ⟫ × ⟪ fst C ⟫` (src/L/InjChain.lagda.md:279) and hands
--   that index type to `StageBound` (:293).  So the bound the code needs
--   is a function of a AND b, and the bound `CodeSelect` offers is a
--   function of a alone.  **THE TWO ARE NOT THE SAME ORDINAL AND
--   NOTHING IN THE TREE MAKES THEM ONE.**
--
--   THAT IS THE FINDING, AND IT IS NOT THE AMBIENT `Inj` COMING BACK.
--   The brief asks to stop and name the projection if a gap needs the
--   ambient injection again.  IT DOES NOT.  Projection 4 wants a STAGE
--   BOUND ON THE CODE.  Nothing below reintroduces `⟪ fst α ⟫ ↪ ⟪ fst γ ⟫`
--   into any predicate.
--
--   WHAT IS PROVED HERE INSTEAD: the selection never needed `SiteBound`.
--   It is generic in ANY (β, oβ).  So the gap NARROWS, from "a code at
--   the β that `SiteBound a` names" to "a β, computed from a and b,
--   holding a code".
-- =====================================================================

module CodeSelectAt (β : V ℓ) (oβ : IsOrd β) (a b : S) where

  upβ : Mem (Lset β) → S
  upβ (x , m) = x , Lset→isL β oβ x m

  -- hProp-VALUED, and NOT a truncation: [LJ-1.576]'s W3 is the second
  -- component, imported and not rebuilt (Probe576.agda:77-84).
  GoodF : Mem (Lset β) → hProp (ℓ-suc ℓ)
  GoodF F = InjCode (upβ F) a b , isPropInjCode (upβ F) a b

  BoundedCodeAt : Type (ℓ-suc ℓ)
  BoundedCodeAt = ∥ Σ[ F ∈ Mem (Lset β) ] ⟨ GoodF F ⟩ ∥₁

  chosen : BoundedCodeAt → Σ[ F ∈ Mem (Lset β) ] IsLeast (orderAt β oβ) GoodF F
  chosen = leastOf (orderAt β oβ) lem GoodF

  bare-code : BoundedCodeAt → Σ[ F ∈ S ] InjCode F a b
  bare-code h = upβ (fst (chosen h)) , fst (snd (chosen h))

  bare-inj : BoundedCodeAt → ⟪ fst a ⟫ ↪ ⟪ fst b ⟫
  bare-inj h = readL a b (bare-code h)

-- THE NARROWED GAP, WRITTEN AS A TYPE AND **NOT INHABITED**.  A β and a
-- code at it, as DATA, out of the truncated coded existence.
StageOfCode : Type (ℓ-suc ℓ)
StageOfCode = (a b : S) → InjL a b
            → Σ[ β ∈ V ℓ ] Σ[ oβ ∈ IsOrd β ] CodeSelectAt.BoundedCodeAt β oβ a b

-- AND HERE IS WHY THAT TYPE IS THE WHOLE OF THE GAP, MEASURED AND NOT
-- ARGUED.  ITS TRUNCATION **IS** INHABITED, WITH NOTHING ASSUMED: every
-- L-set sits in a stage (src/L/Stage.lagda.md:185-188), so a code
-- always has a β.  The Σ is not a proposition, so the β cannot leave
-- the truncation, and `leastOf` needs it OUTSIDE.  **The gap is the
-- truncation boundary and it is not existence.**
stage-of-code-truncated :
    (a b : S) → InjL a b
  → ∥ Σ[ β ∈ V ℓ ] Σ[ oβ ∈ IsOrd β ] CodeSelectAt.BoundedCodeAt β oβ a b ∥₁
stage-of-code-truncated a b = PT.map step
  where
  step : Σ[ F ∈ S ] InjCode F a b
       → Σ[ β ∈ V ℓ ] Σ[ oβ ∈ IsOrd β ] CodeSelectAt.BoundedCodeAt β oβ a b
  step (F , code) =
      stage (fst F) (snd F)
    , stage-ord (fst F) (snd F)
    , ∣ (fst F , stage-mem (fst F) (snd F)) , code ∣₁

-- =====================================================================
-- SECTION 5.  THE OBLIGATION.
--
--   The brief asks for ONE term: "the named GAPS among [LJ-1.576]'s
--   five sealed projections, answered".  Section 1 measured that the
--   named gaps are three.  TWO ARE ANSWERED WITH TERMS.  THE THIRD IS
--   ANSWERED WITH A MEASUREMENT AND NOT WITH A TERM, so it appears in
--   this type as the REDUCTION that is proved and not as a discharge
--   that is not: `stage-of-code-truncated` says the gap is exactly the
--   truncation boundary, and `StageOfCode` above names what is missing.
--
--   NOTHING IN THIS TYPE IS A HYPOTHESIS.  A reader may take every
--   conjunct as delivered.
-- =====================================================================

sealed-gaps-closed :
    -- GAP A, answered.  The identity code, at every L-element.
    IdCoded
    -- GAP A at the row, answered.  `module Five`'s hypothesis, gone.
  × ((α : S) (oα : IsOrd (fst α)) → Coded.Nonemptyᶜ α oα)
    -- GAP C, answered.  Coded composition, at three sets.
  × CodedComp
    -- GAP B, answered as a MEASUREMENT: a code always has a stage, and
    -- the stage cannot leave the truncation.  NOT a discharge of
    -- `CodeBounded`, which stays open.
  × ((a b : S) → InjL a b
       → ∥ Σ[ β ∈ V ℓ ] Σ[ oβ ∈ IsOrd β ]
             CodeSelectAt.BoundedCodeAt β oβ a b ∥₁)
sealed-gaps-closed =
  idCoded , nonemptyᶜ , codedComp , stage-of-code-truncated

-- =====================================================================
-- SECTION 6.  WHAT IS NOT HERE.
--
--   THESE FIVE TYPES ARE NAMED IN THIS FILE AND NONE IS INHABITED:
--
--     CodeBounded   -- GAP B, [LJ-1.576]'s form.  Section 4 measures
--                      that its β is a function of `a` alone and the
--                      code's β reads `b`, so it is not the gap to try.
--     StageOfCode   -- GAP B, the narrowed form.  This IS the gap.
--     SquareCoded   -- the third `κ-min-atL` call site, :109.
--     AmbientCoded  -- what [LJ-1.576]'s section 4 equality needs.
--     CodeUnique    -- not expected to hold.
--
--   NO ROW IS PAID.  `SqCollectAt` is not stated in this file, is not
--   inhabited in this file, and this task did not attempt it: the brief
--   forbids it ("DO NOT BUILD `SqCollectAt` ITSELF").
--
--   AND `sealed-gaps-closed`'s FOURTH CONJUNCT IS NOT A DISCHARGE OF
--   GAP B, which is said here because it is the easiest misreading of
--   this file.  It is a truncated existence.  `CodeSelectAt.bare-inj`
--   consumes `BoundedCodeAt` at a β that is already OUTSIDE a
--   truncation, and the fourth conjunct does not put it there.
--
--   NO POSTULATE.  NO HOLE.  NOTHING UNDER src/.
-- =====================================================================

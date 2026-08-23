{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.601]  MEASURE THE FINITE BASE.
--
-- THE QUESTION, VERBATIM, is [LJ-1.597]'s reopener item 2
-- (agents/tasks/LJ-1-597/review-of-step-graph.md:167-170):
--   "MEASURE THE FINITE BASE. No task has measured whether the `Tally`
--    route (`src/L/Choice/Finite`) has a formula."
-- Stated at the carrier this campaign's internalization reading fixes,
-- it is [LJ-1.597]'s own `Graph` shape at the function part of the
-- route's delivered injection `finite-stage-inj`
-- (src/L/StageCardinal.lagda.md:485): runs/W3.agda carries THAT type
-- alone, `W3.TallyGraph`, and it was written FIRST and typechecked
-- ALONE (runs/w3-1.out, GREEN, 2.22 s; runs/w3-2.out, 1.19 s; cap
-- 120 s).  This file imports it and inhabits it, so the stated
-- statement and the discharged one are one type and cannot drift.
--
-- THE ANSWER IS A MEASUREMENT AND IT IS GO: the graph EXISTS, and the
-- witness is the FINITE TABLE the route itself hands over.  THE TERM
-- IS GREEN, EXIT 0, THREE RUNS AT THE DELIVERED SHAPE (runs/final-4.out
-- at 12.07 s cold, final-5.out at 1.26 s and final-6.out at 1.25 s
-- warm; caliber `-A64m -I0 -M2g`, cap 300 s), and green again before
-- the import trim at final-1.out to final-3.out.  It carries no hole
-- and no postulate, `--safe` is on, and nothing landed in `src/`.  The
-- FLOOR was measured BEFORE the proof (runs/floor-3.out: the same file
-- with the obligation's assembly as a hole, 11.57 s, exit 42 at the
-- hole and nowhere else), per the owner's ruling of 2026-08-23.
--
-- NO ROW puts `stageOrder`, `finite-stage-inj` or `stage-card-upper`
-- into a conversion problem as a SCRUTINEE: [LJ-1.584] measured that
-- one such row does not terminate
-- (agents/tasks/LJ-1-584/runs/w3b-1.out).  They appear in TYPES, in
-- projections of computed pairs, and under `refl` at section 1, where
-- the equation is one delta step each.
--
--   Section 0.  W3, imported.  The statement, and the lifts it names.
--   Section 1.  THE VALUE EQUATION AT THE FINITE BASE, three `refl`
--               rows.  The analogue of [LJ-1.594]'s two, at this site.
--   Section 2.  THE TABLE FORMULA and its plumbing.
--   Section 3.  THE CONGRUENCE the table needs: `h` at equal members.
--   Section 4.  THE OBLIGATION, both directions.
--
-- CALIBER.  THE PROGRAM SET GHCRTS ON THIS PANE.  I DID NOT SET IT.
-- ONE AGDA PROCESS AT A TIME.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open import L.Constructible using ( IsOrd )
import Cubical.Data.Empty as Empty

module LJ-1-601.Probe601 {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
  (α₀ : V ℓ) (oα₀ : IsOrd α₀)
  (sq : (δ : V ℓ) → ⟨ δ ∈ InfinitySet.sucV α₀ ⟩ → (⟨ δ ∈ InfinitySet.ω {ℓ} ⟩ → Empty.⊥)
      → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
          ((x y : ⟪ δ ⟫ × ⟪ δ ⟫) → f x ≡ f y → x ≡ y)) where

open import FOL.Syntax using ( Formula; con; var; _≐_; _∧̇_; _∨̇_; ⊥̇ )
open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Presentation {ℓ} using ( member; fiber )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Choice.Finite {ℓ} lem using ( Tally; StageOrder; stageOrder; finiteStage )
import L.StageCardinal

open import Cubical.Foundations.Prelude using ( J )
open import Cubical.Data.Sum using ( inl; inr )
open Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫↪ )
open InfinitySet {ℓ} using ( ω )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
module SV = hPropStructure 𝒮ᵥ
module SL = hPropStructure 𝒮ʟ
open SV using ( _∈ˢ_; isSetS )
open SL using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

module SC = L.StageCardinal {ℓ} lem α₀ oα₀ sq

-- THE STATEMENT, imported from the slice that typechecked it alone.
import LJ-1-601.runs.W3 {ℓ} lem α₀ oα₀ sq as W3


-- ===================================================================
-- SECTION 0.  W3, IMPORTED.
--
--   `W3.TallyGraph n` is the `Tally` question as a type: a `Formula
--   S 2`, value first and index second, with BOTH readings
--   (the `Definition` shape, src/L/Recursion.lagda.md:272-279), at
--   `finite-stage-inj`'s function part read on the members of the
--   finite stage.  `W3.val` is that function part lifted to an
--   L-element of `ω`; `W3.dom` is the stage as an L-element, and
--   `fst (W3.dom n)` IS `finiteStage n` (`Lset (# n)`), so membership
--   in the domain is membership in the finite stage.
-- ===================================================================


-- ===================================================================
-- SECTION 1.  THE VALUE EQUATION AT THE FINITE BASE, BY `refl`.
--
--   Three rows, each one delta step, in [LJ-1.594]'s discipline.  WHAT
--   THE BASE'S VALUE IS: `fst (finite-stage-inj n)` at a presentation
--   is `FinInj.h` at the underlying member (1.1); `h` at a member is
--   the numeral of `least` (1.2); the lift `val` reads through `⟪ ω ⟫↪`
--   (1.3).  Together: the finite base's value at a member is THE
--   NUMERAL OF THE LEAST TALLY INDEX OF THAT MEMBER.
--
--   THE VALUE PATH NAMES NO `sq`.  A reading of the chain, not a
--   proved row: `finite-stage-inj` is `FinInj.stage-inj`
--   (src/L/StageCardinal.lagda.md:485), whose value is `h`
--   (:462-463), whose value is `numeralω (least x x∈)` (:465-466),
--   and `least` is `leastOf natOrder` (:452-453) over the tally's
--   `onto` (:448-449).  The pairing parameter `sq` (:17-19) enters the
--   step only through `LimitStep` (:396-403), which the finite base
--   never reaches.  The whole step's graph carries ingredient (iii);
--   ITS OWN base carries none of it.
-- ===================================================================

-- 1.1  THE FUNCTION PART, AT A PRESENTATION.
fin-val-eq : (n : ℕ) (m : ⟪ finiteStage n ⟫)
  → fst (W3.fin-base n) m
    ≡ SC.FinInj.h n (StageOrder.tally (stageOrder n))
        (⟪ finiteStage n ⟫↪ m) (member (finiteStage n) m)
fin-val-eq n m = refl

-- 1.2  `h` IS THE NUMERAL OF THE LEAST INDEX.
fin-h-eq : (n : ℕ) (x : V ℓ) (x∈ : ⟨ x ∈ˢ finiteStage n ⟩)
  → SC.FinInj.h n (StageOrder.tally (stageOrder n)) x x∈
    ≡ SC.numeralω (SC.FinInj.least n (StageOrder.tally (stageOrder n)) x x∈)
fin-h-eq n x x∈ = refl

-- 1.3  THE LIFT READS THROUGH `⟪ ω ⟫↪`.
val-lift-eq : (n : ℕ) (x : S) (m : ⟨ fst x ∈ fst (W3.dom n) ⟩)
  → fst (W3.val n x m)
    ≡ ⟪ ω ⟫↪ (fst (W3.fin-base n) (fiber (fst (W3.dom n)) m .fst))
val-lift-eq n x m = refl


-- ===================================================================
-- SECTION 2.  THE TABLE FORMULA, AND ITS PLUMBING.
--
--   The tally of the finite stage, named once (2.1), its entries as
--   formula constants (2.2), the clause "x is entry i and y is entry
--   i's value" (2.3), and the finite disjunction over the table
--   (2.4), [LJ-1.594]'s `finDisj` at arity 2.  The satisfaction
--   plumbing (2.5, 2.6) is generic in the disjunction.
-- ===================================================================

-- 2.1  THE TALLY, NAMED ONCE.  This is the instance
--      `finite-stage-inj` itself uses (src/L/StageCardinal.lagda.md:
--      485).
tallyOf : (n : ℕ) → Tally (finiteStage n)
tallyOf n = StageOrder.tally (stageOrder n)

sizeOf : (n : ℕ) → ℕ
sizeOf n = Tally.size (tallyOf n)

itemOf : (n : ℕ) (i : Fin (sizeOf n)) → V ℓ
itemOf n i = Tally.item (tallyOf n) i

insideOf : (n : ℕ) (i : Fin (sizeOf n)) → ⟨ itemOf n i ∈ˢ finiteStage n ⟩
insideOf n i = Tally.inside (tallyOf n) i

ontoOf : (n : ℕ) (x : V ℓ) (x∈ : ⟨ x ∈ˢ finiteStage n ⟩)
  → ∥ Σ[ i ∈ Fin (sizeOf n) ] (itemOf n i ≡ x) ∥₁
ontoOf n x x∈ = Tally.onto (tallyOf n) x x∈

-- 2.2  THE CONSTANTS.  The entry as an L-element of the domain, the
--      entry's value as an L-element of `ω`.  `fiber ... .snd` is the
--      specification of the first: its underlying set IS the entry.
X : (n : ℕ) (i : Fin (sizeOf n)) → S
X n i = W3.up (W3.dom n)
  (fiber (finiteStage n) {x = itemOf n i} (insideOf n i) .fst)

Y : (n : ℕ) (i : Fin (sizeOf n)) → S
Y n i = W3.up W3.ωS
  (SC.FinInj.h n (tallyOf n) (itemOf n i) (insideOf n i))

-- 2.3  THE CLAUSE.  Variable 1 is the index, variable 0 is the value,
--      the order `y ∷ x ∷ []` fixes (value first, index second).
cl : (n : ℕ) (i : Fin (sizeOf n)) → Formula S 2
cl n i = (var (suc zero) ≐ con (X n i)) ∧̇ (var zero ≐ con (Y n i))

-- 2.4  THE DISJUNCTION.
bigDisj : (k : ℕ) → (Fin k → Formula S 2) → Formula S 2
bigDisj zero    g = ⊥̇
bigDisj (suc k) g = g zero ∨̇ bigDisj k (λ i → g (suc i))

ψ : (n : ℕ) → Formula S 2
ψ n = bigDisj (sizeOf n) (cl n)

-- 2.5  SATISFACTION AT ONE CLAUSE GIVES SATISFACTION OF THE TABLE.
bigDisj-in : (k : ℕ) (g : Fin k → Formula S 2) (env : S ^ 2) (i : Fin k)
  → ⟨ env ⊨ g i ⟩ → ⟨ env ⊨ bigDisj k g ⟩
bigDisj-in zero    g env ()
bigDisj-in (suc k) g env zero    h = ∣ inl h ∣₁
bigDisj-in (suc k) g env (suc i) h =
  ∣ inr (bigDisj-in k (λ j → g (suc j)) env i h) ∣₁

-- 2.6  SATISFACTION OF THE TABLE NAMES A CLAUSE, MERELY.
bigDisj-out : (k : ℕ) (g : Fin k → Formula S 2) (env : S ^ 2)
  → ⟨ env ⊨ bigDisj k g ⟩ → ∥ Σ[ i ∈ Fin k ] ⟨ env ⊨ g i ⟩ ∥₁
bigDisj-out zero    g env h = Empty.rec* h
bigDisj-out (suc k) g env h =
  PT.rec squash₁
    (λ { (inl p) → ∣ zero , p ∣₁
       ; (inr q) → PT.map (λ { (i , s) → suc i , s })
                          (bigDisj-out k (λ j → g (suc j)) env q) })
    h


-- ===================================================================
-- SECTION 3.  THE CONGRUENCE THE TABLE NEEDS.
--
--   `h` at a member depends on the member and its membership proof,
--   and membership is a proposition, so `h` agrees at equal members
--   (3.2).  At a domain member `x` and ANY tally entry equal to it,
--   the base's value at `x` and `h` at that entry are one value
--   (3.3).  Nothing here computes a `least`: the rows are `cong` and
--   `J` over proof-irrelevant membership, so no `leastOf`, no tally
--   recursion and no mask enumeration is ever forced.
-- ===================================================================

-- 3.1  `least` IS STABLE UNDER THE MEMBERSHIP PROOF.
least-stable : (n : ℕ) (z : V ℓ) (z∈ w : ⟨ z ∈ˢ finiteStage n ⟩)
  → SC.FinInj.least n (tallyOf n) z z∈ ≡ SC.FinInj.least n (tallyOf n) z w
least-stable n z z∈ w =
  cong (SC.FinInj.least n (tallyOf n) z) (snd (z ∈ˢ finiteStage n) z∈ w)

-- 3.2  `h` AGREES AT EQUAL MEMBERS.
h-cong : (n : ℕ) (z z' : V ℓ) (p : z ≡ z')
  (z∈ : ⟨ z ∈ˢ finiteStage n ⟩) (z'∈ : ⟨ z' ∈ˢ finiteStage n ⟩)
  → SC.FinInj.h n (tallyOf n) z z∈ ≡ SC.FinInj.h n (tallyOf n) z' z'∈
h-cong n z z' p z∈ z'∈ =
  J (λ z' p → (w : ⟨ z' ∈ˢ finiteStage n ⟩)
            → SC.FinInj.h n (tallyOf n) z z∈ ≡ SC.FinInj.h n (tallyOf n) z' w)
    (λ w → cong SC.numeralω (least-stable n z z∈ w))
    p z'∈

-- 3.3  THE VALUE AT A MEMBER IS `h` AT ANY ENTRY EQUAL TO IT.
val-item-eq : (n : ℕ) (x : S) (m : ⟨ fst x ∈ fst (W3.dom n) ⟩)
  (i : Fin (sizeOf n)) (q : itemOf n i ≡ fst x)
  → fst (W3.val n x m) ≡ fst (Y n i)
val-item-eq n x m i q =
  cong (⟪ ω ⟫↪)
    ( fin-val-eq n (fiber (fst (W3.dom n)) m .fst)
    ∙ h-cong n (⟪ finiteStage n ⟫↪ (fiber (fst (W3.dom n)) m .fst))
        (itemOf n i)
        ( fiber (fst (W3.dom n)) m .snd ∙ sym q )
        ( member (finiteStage n) (fiber (fst (W3.dom n)) m .fst) )
        ( insideOf n i ) )


-- ===================================================================
-- SECTION 4.  THE OBLIGATION, BOTH DIRECTIONS.
--
--   `defines`: at a domain member, the table holds at its own value,
--   by the tally's `onto`, at the entry it names.  `only`: whatever
--   satisfies the table is that entry's value, and 3.3 says the
--   member's value is the same one.  THE TERM IS THE MEASUREMENT:
--   the Tally route HAS a formula, namely the table.
-- ===================================================================

defines-side : (n : ℕ) (x y : S) (m : ⟨ fst x ∈ fst (W3.dom n) ⟩)
  → fst y ≡ fst (W3.val n x m) → ⟨ (y ∷ x ∷ []) ⊨ ψ n ⟩
defines-side n x y m e =
  PT.rec (snd ((y ∷ x ∷ []) ⊨ ψ n)) mk (ontoOf n (fst x) m)
  where
  mk : Σ[ i ∈ Fin (sizeOf n) ] (itemOf n i ≡ fst x)
     → ⟨ (y ∷ x ∷ []) ⊨ ψ n ⟩
  mk (i , q) =
    bigDisj-in (sizeOf n) (cl n) (y ∷ x ∷ []) i
      ( ( sym q
          ∙ sym (fiber (finiteStage n) {x = itemOf n i} (insideOf n i) .snd) )
      , ( e ∙ val-item-eq n x m i q ) )

only-side : (n : ℕ) (x y : S) → ⟨ (y ∷ x ∷ []) ⊨ ψ n ⟩
  → (m : ⟨ fst x ∈ fst (W3.dom n) ⟩) → fst y ≡ fst (W3.val n x m)
only-side n x y sat m =
  PT.rec (isSetS (fst y) (fst (W3.val n x m))) mk
    (bigDisj-out (sizeOf n) (cl n) (y ∷ x ∷ []) sat)
  where
  mk : Σ[ i ∈ Fin (sizeOf n) ] ⟨ (y ∷ x ∷ []) ⊨ cl n i ⟩
     → fst y ≡ fst (W3.val n x m)
  mk (i , cx , cy) = cy ∙ sym (val-item-eq n x m i q)
    where
    q : itemOf n i ≡ fst x
    q = sym (cx
          ∙ fiber (finiteStage n) {x = itemOf n i} (insideOf n i) .snd)

finite-base-measured : (n : ℕ) → W3.TallyGraph n
finite-base-measured n = ψ n , ( defines-side n , only-side n )

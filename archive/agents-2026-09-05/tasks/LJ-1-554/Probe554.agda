{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.554]  Can a formula describe an assignment it was not built with.
--
-- W3 IS agents/tasks/LJ-1-554/runs/W3.agda, WRITTEN FIRST AND
-- TYPECHECKED ALONE, runs w3-1.out to w3-3.out, exit 0.  The reading
-- forms at arity 3 with nothing else in scope.
--
-- NEITHER `no-generic-link` NOR THE GENERIC `Link` IS IN THIS FILE.
-- The brief said one of the two is true and the task is to find out
-- which.  THE MEASURED ANSWER IS THAT NEITHER IS REACHABLE HERE, and
-- the stop is agents/tasks/LJ-1-554/review-of-no-generic-link.md.
--
-- THIS FILE CARRIES NO HOLE AND NO POSTULATE.  That is deliberate and
-- it is the `[LJ-1.533]` discipline: a hole would make every reduction
-- in it a claim, and green makes each one a measurement.  Nothing
-- lands in src/.
--
-- WHAT THE FILE MEASURES, ONE LINE EACH.
--
--   Section 0.  The obligation's type, and that it IS `[LJ-1.549]`'s
--               `Residue` and not a paraphrase of it.
--   Section 1.  D-10, BEFORE ANY OTHER AGDA.  The counting the brief
--               offered DOES NOT FIRE.  `Formula S 3` names every
--               L-set, and the assignment's graph is already an
--               ambient set with no hypothesis.
--   Section 2.  `Link` and the CODED GRAPH are the same request.
--               Both directions, no hypothesis left over.
--   Section 3.  The one property of `s` that buys a `Link` is
--               `⟨ isL (grV δ s) ⟩`, and it is not a size condition.
--   Section 4.  The three generic statements and the arithmetic.
--   Section 5.  Why the obligation is absent.
--   Section 6.  The sweep (C-42).
--
-- CALIBER.  The program set GHCRTS="-A64m -I0 -M8g" on this pane.  I
-- did not set it.  One Agda process at a time.  No heap event.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-554.Probe554 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; Term; var; con; _∈̇_; _≐_; _∧̇_; ∃̇_ )
import FOL.Absoluteness
import FOL.ZFModel
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; pr-inj )
open import V.Presentation {ℓ} using ( ↪-inj )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Coding.Model {ℓ}
  using ( prAtL; prAtL-adequate; prʟ; prʟ-fst )

open import Cubical.Data.FinData using ( Fin; zero; suc )
open import Cubical.Data.Sigma using ( _×_ )
open import Cubical.HITs.CumulativeHierarchy.Base
  using ( V; _∈_; sett; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪ )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )

import LJ-1-549.Probe549 {ℓ} lem as P549

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )

module ModelL = FOL.ZFModel 𝒮ʟ
open ModelL using ( _⊆ˢ_ )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- =====================================================================
-- SECTION 0.  THE OBLIGATION'S TYPE, WRITTEN OUT.
-- =====================================================================

LinkAt : (δ : S) (s : ⟪ fst δ ⟫ → S) → Type (ℓ-suc ℓ)
LinkAt δ s =
  Σ[ Link ∈ Formula S 3 ]
    ( ((x y z : S) (m : ⟨ fst x ∈ fst δ ⟩) → fst y ≡ fst (s (P549.ixOf δ x m))
       → ⟨ (y ∷ x ∷ z ∷ []) ⊨ Link ⟩)
    × ((x y z : S) → ⟨ (y ∷ x ∷ z ∷ []) ⊨ Link ⟩
       → (m : ⟨ fst x ∈ fst δ ⟩) → fst y ≡ fst (s (P549.ixOf δ x m))) )

GenericLink : Type (ℓ-suc ℓ)
GenericLink =
    (δ κ : S) (s : ⟪ fst δ ⟫ → S)
  → ((k : ⟪ fst δ ⟫) → ⟨ s k ⊆ˢ κ ⟩)
  → ((k k' : ⟪ fst δ ⟫) → fst (s k) ≡ fst (s k') → k ≡ k')
  → LinkAt δ s

NoGenericLinkᵀ : Type (ℓ-suc ℓ)
NoGenericLinkᵀ = GenericLink → Empty.⊥

-- THE TYPE IS `[LJ-1.549]`'s RESIDUE AND NOT A PARAPHRASE OF IT.
generic→residue :
    GenericLink
  → (δ κ : S) (s : ⟪ fst δ ⟫ → S)
  → ((k : ⟪ fst δ ⟫) → ⟨ s k ⊆ˢ κ ⟩)
  → ((k k' : ⟪ fst δ ⟫) → fst (s k) ≡ fst (s k') → k ≡ k')
  → P549.Residue δ κ
generic→residue G δ κ s sub inj = s , (sub , (inj , G δ κ s sub inj))

residue→generic :
    ((δ κ : S) (s : ⟪ fst δ ⟫ → S)
     → ((k : ⟪ fst δ ⟫) → ⟨ s k ⊆ˢ κ ⟩)
     → ((k k' : ⟪ fst δ ⟫) → fst (s k) ≡ fst (s k') → k ≡ k')
     → LinkAt δ s)
  → GenericLink
residue→generic f = f

-- =====================================================================
-- SECTION 1.  D-10, BEFORE ANY OTHER AGDA, AND IT IS THE COUNTING.
--
--   THE BRIEF ORDERED THE COUNTING AND OFFERED ITS ANSWER: "If the
--   formulas are a set and the assignments are a function space into
--   a proper carrier, say so: that is the whole argument and the rest
--   is writing it down."
--
--   THE COUNTING DOES NOT FIRE, AND THE TREE SAYS SO IN ITS OWN
--   PROSE.  `src/FOL/Syntax.lagda.md:138`: "a syntax whose constants
--   are all sets is too big to be counted or coded".  `Formula S 3`
--   is that syntax: `K := S`, the L-carrier itself.
--
--   TWO MEASUREMENTS BELOW, and neither is a reading.
-- =====================================================================

-- MEASUREMENT 1.  EVERY L-SET IS A CONSTANT OF `Formula S 3`, and the
-- naming is injective.  So `Formula S 3` is at least as wide as `S`.
-- `con : K → Term K n` is src/FOL/Syntax.lagda.md:43.

private
  tmCon : Term S 3 → S → S
  tmCon (con c) _ = c
  tmCon (var _) d = d

  atomL : Formula S 3 → S → S
  atomL (t ∈̇ _) d = tmCon t d
  atomL _       d = d

nameOf : S → Formula S 3
nameOf c = con c ∈̇ var zero

nameOf-inj : (c c' : S) → nameOf c ≡ nameOf c' → c ≡ c'
nameOf-inj c c' p = cong (λ φ → atomL φ c') p

-- MEASUREMENT 2.  THE ASSIGNMENT'S GRAPH IS ALREADY AN AMBIENT SET,
-- WITH NO HYPOTHESIS AT ALL.  `sett` takes any SMALL family of
-- ambient sets to one ambient set, and `⟪ fst δ ⟫` is small by
-- construction.  Membership in it is definitional, so both readings
-- below are the identity function.
--
-- THIS IS THE WHOLE SHAPE OF THE ANSWER.  Nothing is missing
-- AMBIENTLY.  What is missing is `isL` of this set, and `isL` is not
-- a size condition.

grV : (δ : S) (s : ⟪ fst δ ⟫ → S) → V ℓ
grV δ s = sett ⟪ fst δ ⟫ (λ k → pr (⟪ fst δ ⟫↪ k) (fst (s k)))

grV-in : (δ : S) (s : ⟪ fst δ ⟫ → S) (k : ⟪ fst δ ⟫)
       → ⟨ pr (⟪ fst δ ⟫↪ k) (fst (s k)) ∈ grV δ s ⟩
grV-in δ s k = ∣ k , refl ∣₁

grV-out : (δ : S) (s : ⟪ fst δ ⟫ → S) (a : V ℓ)
        → ⟨ a ∈ grV δ s ⟩
        → ∥ Σ[ k ∈ ⟪ fst δ ⟫ ] (pr (⟪ fst δ ⟫↪ k) (fst (s k)) ≡ a) ∥₁
grV-out δ s a h = h

-- =====================================================================
-- SECTION 2.  WHAT A `Link` IS, MEASURED IN BOTH DIRECTIONS.
--
--   `IsGraphOf δ s G` says: the L-element `G` has, as members, exactly
--   the ordered pairs of the assignment.  Nothing syntactic is in it.
--
--   SECTION 2A.  A `Link` GIVES SUCH A `G`.  This is `[LJ-1.549]`'s
--   `module Table` and I do not rebuild one line of it: the separation
--   it runs is what carves `G` out of the bound, and `Link` is the only
--   input of that separation this tree cannot supply.
--
--   SECTION 2B.  SUCH A `G` GIVES A `Link`.  One `∃̇`, one `prAtL`, one
--   `∈̇ con G`.  Nine lines of formula and two readings.
--
--   TOGETHER THEY SAY THE TWO ARE THE SAME REQUEST.  That is the whole
--   result of this task and section 3 spends it.
-- =====================================================================

IsGraphOf : (δ : S) (s : ⟪ fst δ ⟫ → S) (G : S) → Type (ℓ-suc ℓ)
IsGraphOf δ s G =
    ((x y : S) (m : ⟨ fst x ∈ fst δ ⟩) → fst y ≡ fst (s (P549.ixOf δ x m))
     → ⟨ pr (fst x) (fst y) ∈ fst G ⟩)
  × ((x y : S) → ⟨ pr (fst x) (fst y) ∈ fst G ⟩
     → (m : ⟨ fst x ∈ fst δ ⟩) → fst y ≡ fst (s (P549.ixOf δ x m)))

-- SECTION 2A.  `Link` BUYS THE CODED GRAPH.
link→graph :
    (δ κ : S) (s : ⟪ fst δ ⟫ → S)
  → (sub : (k : ⟪ fst δ ⟫) → ⟨ s k ⊆ˢ κ ⟩)
  → (inj : (k k' : ⟪ fst δ ⟫) → fst (s k) ≡ fst (s k') → k ≡ k')
  → LinkAt δ s
  → Σ[ G ∈ S ] IsGraphOf δ s G
link→graph δ κ s sub inj (Link , (lin , lout)) = T.G , (gin , T.graph-val)
  where
  module T = P549.Table δ κ s sub inj Link lin lout

  gin : (x y : S) (m : ⟨ fst x ∈ fst δ ⟩) → fst y ≡ fst (s (P549.ixOf δ x m))
      → ⟨ pr (fst x) (fst y) ∈ fst T.G ⟩
  gin x y m e =
    subst (λ t → ⟨ pr (fst x) t ∈ fst T.G ⟩) (sym e) (T.graph-in x m)

-- SECTION 2B.  THE CODED GRAPH BUYS `Link`.  NO κ, NO `⊆ˢ`, NO
-- INJECTIVITY: the converse is cheaper than the forward direction and
-- needs none of the three side conditions.
--
--   ARITY 3, environment (y ∷ x ∷ z ∷ []).  Under the one binder the
--   environment is (w ∷ y ∷ x ∷ z ∷ []) and the slots are
--
--       var 0 = w, the pair      var 1 = y, the value
--       var 2 = x, the argument  var 3 = z, unused
--
--   `z` IS UNUSED HERE AND THAT IS NOT AN ACCIDENT.  `[LJ-1.549]`'s
--   `Residue` quantifies `Link`'s readings over `z` with no condition
--   on it, so the third slot is free, and a `Link` that ignores it
--   satisfies both readings.

LinkFo : S → Formula S 3
LinkFo G =
  ∃̇ ( prAtL zero (suc (suc zero)) (suc zero) ∧̇ (var zero ∈̇ con G) )

graph→link :
    (δ : S) (s : ⟪ fst δ ⟫ → S) (G : S)
  → IsGraphOf δ s G → LinkAt δ s
graph→link δ s G (gin , gout) = LinkFo G , (lin , lout)
  where
  lin : (x y z : S) (m : ⟨ fst x ∈ fst δ ⟩) → fst y ≡ fst (s (P549.ixOf δ x m))
      → ⟨ (y ∷ x ∷ z ∷ []) ⊨ LinkFo G ⟩
  lin x y z m e = ∣ prʟ x y , (hpr , hin) ∣₁
    where
    hpr : ⟨ (prʟ x y ∷ y ∷ x ∷ z ∷ [])
            ⊨ prAtL zero (suc (suc zero)) (suc zero) ⟩
    hpr = subst ⟨_⟩
      (sym (prAtL-adequate zero (suc (suc zero)) (suc zero)
             (prʟ x y ∷ y ∷ x ∷ z ∷ [])))
      (prʟ-fst x y)

    hin : ⟨ fst (prʟ x y) ∈ fst G ⟩
    hin = subst (λ t → ⟨ t ∈ fst G ⟩) (sym (prʟ-fst x y)) (gin x y m e)

  lout : (x y z : S) → ⟨ (y ∷ x ∷ z ∷ []) ⊨ LinkFo G ⟩
       → (m : ⟨ fst x ∈ fst δ ⟩) → fst y ≡ fst (s (P549.ixOf δ x m))
  lout x y z h m =
    PT.rec (setIsSet (fst y) (fst (s (P549.ixOf δ x m)))) go h
    where
    go : Σ[ w ∈ S ] ⟨ (w ∷ y ∷ x ∷ z ∷ [])
                      ⊨ ( prAtL zero (suc (suc zero)) (suc zero)
                        ∧̇ (var zero ∈̇ con G) ) ⟩
       → fst y ≡ fst (s (P549.ixOf δ x m))
    go (w , (hpr , hw)) = gout x y (subst (λ t → ⟨ t ∈ fst G ⟩) e hw) m
      where
      e : fst w ≡ pr (fst x) (fst y)
      e = subst ⟨_⟩
        (prAtL-adequate zero (suc (suc zero)) (suc zero)
          (w ∷ y ∷ x ∷ z ∷ [])) hpr

-- =====================================================================
-- SECTION 3.  THE ONE PROPERTY OF `s` THAT BUYS A `Link`, AND IT IS
--             NOT A SIZE CONDITION.
--
--   Section 1's `grV δ s` is the assignment's graph AS AN AMBIENT SET.
--   It costs no hypothesis.  Below, `isL` of that one set buys the
--   whole `Link`, through section 2B and nothing else.
--
--   SO THE MISSING INPUT IS NAMED, AND IT IS ONE PROPOSITION:
--   `⟨ isL (grV δ s) ⟩`.  Not a bound (section 1 shows the ambient set
--   exists), not a Levy grade (nothing here is graded), not a count
--   (section 1 shows the count does not fire).
-- =====================================================================

grL : (δ : S) (s : ⟪ fst δ ⟫ → S) → ⟨ isL (grV δ s) ⟩ → S
grL δ s h = grV δ s , h

grL-isGraph : (δ : S) (s : ⟪ fst δ ⟫ → S) (h : ⟨ isL (grV δ s) ⟩)
            → IsGraphOf δ s (grL δ s h)
grL-isGraph δ s h = gin , gout
  where
  gin : (x y : S) (m : ⟨ fst x ∈ fst δ ⟩) → fst y ≡ fst (s (P549.ixOf δ x m))
      → ⟨ pr (fst x) (fst y) ∈ grV δ s ⟩
  gin x y m e = subst (λ t → ⟨ t ∈ grV δ s ⟩)
    (cong₂ pr (P549.ixOf-val δ x m) (sym e))
    (grV-in δ s (P549.ixOf δ x m))

  gout : (x y : S) → ⟨ pr (fst x) (fst y) ∈ grV δ s ⟩
       → (m : ⟨ fst x ∈ fst δ ⟩) → fst y ≡ fst (s (P549.ixOf δ x m))
  gout x y hp m =
    PT.rec (setIsSet (fst y) (fst (s (P549.ixOf δ x m)))) go hp
    where
    go : Σ[ k ∈ ⟪ fst δ ⟫ ]
           (pr (⟪ fst δ ⟫↪ k) (fst (s k)) ≡ pr (fst x) (fst y))
       → fst y ≡ fst (s (P549.ixOf δ x m))
    go (k , q) = sym (pr-inj q .snd) ∙ cong (λ t → fst (s t)) kk
      where
      kk : k ≡ P549.ixOf δ x m
      kk = ↪-inj {a = fst δ} (pr-inj q .fst ∙ sym (P549.ixOf-val δ x m))

constructible-graph→link :
    (δ : S) (s : ⟪ fst δ ⟫ → S) → ⟨ isL (grV δ s) ⟩ → LinkAt δ s
constructible-graph→link δ s h = graph→link δ s (grL δ s h) (grL-isGraph δ s h)

-- =====================================================================
-- SECTION 4.  THE THREE GENERIC STATEMENTS, AND THE ARITHMETIC.
--
--       GenericConstructible  ⟹  GenericLink  ⟺  GenericGraph
--
--   THE OBLIGATION IS `GenericLink → ⊥`.  By the middle equivalence it
--   is `GenericGraph → ⊥`, and by the left arrow anything that refutes
--   it also refutes `GenericConstructible`.
--
--   `GenericConstructible` SAYS: the graph of an ARBITRARY ambient
--   injective assignment of subsets of κ is constructible.  That is
--   `[LJ-1.414]`'s HALF A at this site.  Section 5 says what refuting
--   it would cost.
--
--   THE ARROW I DID NOT BUILD, STATED AS A LIMIT.
--   `GenericGraph → GenericConstructible` is NOT built and I do not
--   claim it.  `IsGraphOf δ s G` constrains only the PAIR members of
--   `G`, so a witness may carry junk and need not be `grV δ s` on the
--   nose.  The triangle is a triangle and not a cycle.
-- =====================================================================

GenericGraph : Type (ℓ-suc ℓ)
GenericGraph =
    (δ κ : S) (s : ⟪ fst δ ⟫ → S)
  → ((k : ⟪ fst δ ⟫) → ⟨ s k ⊆ˢ κ ⟩)
  → ((k k' : ⟪ fst δ ⟫) → fst (s k) ≡ fst (s k') → k ≡ k')
  → Σ[ G ∈ S ] IsGraphOf δ s G

GenericConstructible : Type (ℓ-suc ℓ)
GenericConstructible =
    (δ κ : S) (s : ⟪ fst δ ⟫ → S)
  → ((k : ⟪ fst δ ⟫) → ⟨ s k ⊆ˢ κ ⟩)
  → ((k k' : ⟪ fst δ ⟫) → fst (s k) ≡ fst (s k') → k ≡ k')
  → ⟨ isL (grV δ s) ⟩

generic-link→generic-graph : GenericLink → GenericGraph
generic-link→generic-graph F δ κ s sub inj =
  link→graph δ κ s sub inj (F δ κ s sub inj)

generic-graph→generic-link : GenericGraph → GenericLink
generic-graph→generic-link F δ κ s sub inj =
  graph→link δ s (F δ κ s sub inj .fst) (F δ κ s sub inj .snd)

generic-isL→generic-link : GenericConstructible → GenericLink
generic-isL→generic-link F δ κ s sub inj =
  constructible-graph→link δ s (F δ κ s sub inj)

-- AND THE CONTRAPOSITIVES, so the obligation's cost is a term and not
-- a sentence of the report.
no-link→no-graph : NoGenericLinkᵀ → (GenericGraph → Empty.⊥)
no-link→no-graph nl F = nl (generic-graph→generic-link F)

no-link→no-constructible : NoGenericLinkᵀ → (GenericConstructible → Empty.⊥)
no-link→no-constructible nl F = nl (generic-isL→generic-link F)

-- =====================================================================
-- SECTION 5.  THE OBLIGATION IS NOT INHABITED, AND THIS FILE CARRIES
--             NO HOLE THAT PRETENDS OTHERWISE.
--
--   `no-generic-link : NoGenericLinkᵀ` IS ABSENT.  The stop is
--   agents/tasks/LJ-1-554/review-of-no-generic-link.md.
--
--   WHY, IN ONE LINE.  By `no-link→no-constructible`, an inhabitant of
--   `NoGenericLinkᵀ` refutes `GenericConstructible`.  Refuting it needs
--   ONE ambient set that is provably not constructible.  NO TERM OF
--   `src/` REFUTES `isL` OF ANYTHING: the sweep is in the report.
--
--   AND THE TREE HAS ALREADY RECORDED THAT THIS DIRECTION IS
--   INDEPENDENT RATHER THAN FALSE, at the sibling site:
--   dev/memos/2026-08-16-pause.md:515-518.  `[LJ-1.300]` corrected
--   `[LJ-1.299]`'s label there: the ambient-to-coded crossing is TRUE
--   whenever the ambient universe satisfies V=L, and FALSE under a
--   Levy collapse, so "no proof and no countermodel can settle it
--   inside this development".
--
--   THAT MEMO IS A MEASUREMENT AT ANOTHER SITE AND A MEASURED CURE
--   DOES NOT TRANSFER BY ANALOGY.  Sections 2 to 4 are the
--   re-measurement HERE: they turn the arity-3 `Link` of
--   `[LJ-1.549]`'s `Residue` into exactly that crossing, both
--   directions, with no hypothesis left over.
-- =====================================================================

-- =====================================================================
-- SECTION 6.  THE SWEEP (C-42).
--
--   A refutation measures ONE site.  This task's finding is not a
--   refutation, but the law's question is the same: how far does the
--   shape extend?  THE SHAPE IS "a residue that asks an L-element to
--   describe an object the tree has only as an ambient function".
--
--   THE COUNT IS SIX, AND THIS TASK IS THE SIXTH.  Every row is a
--   RECORDED stop and not a reading:
--
--     [LJ-1.414]  agents/tasks/LJ-1-414/review-of-amb-to-coded.md:34
--                 HALF A, the generic crossing.  "no producer for this
--                 type at an arbitrary ambient injection" (:41).
--     [LJ-1.441]  agents/tasks/LJ-1-441/review-of-amb-to-coded-at-least.md:3
--                 the same wall at one named map.
--     [LJ-1.526]  agents/tasks/LJ-1-526/Probe526.agda:110-116.  The
--                 converse of the cardinal readback, STATED AND NOT
--                 INHABITED, with the same reason in its comment.
--     [LJ-1.533]  agents/tasks/LJ-1-533/review-of-StageCountedCoded.md:1
--                 B9.  Its report's sweep counted 5 carving sites in
--                 src/, all 5 with a `Formula`, 0 taking a bare `↪`.
--     [LJ-1.549]  agents/tasks/LJ-1-549/review-of-succ-into-subsets.md:63
--                 B10.  Names `s` and `Link` as the two missing inputs.
--     [LJ-1.554]  this file.  `Link` alone, and it is the same wall.
--
--   ONE ROW LOOKS LIKE THE SHAPE AND IS NOT.  `[LJ-1.535]`
--   (agents/tasks/LJ-1-535/review-of-stage-card-upper-coded.md:8-14)
--   BUILT its Formula-carrying restatement and green.  Its block is
--   that the formula does not reach the injection's VALUE.  That is a
--   statement about where a delivered formula travels, not about a
--   formula that has no producer.  It is a NEIGHBOUR and I do not
--   count it.
--
--   WHAT THE SWEEP DOES NOT MEASURE, STATED AS A LIMIT.  I counted
--   RECORDED stops, which is what the tree can show me.  I did not
--   count the rows of the campaign that will meet this wall and have
--   not been dispatched, and I cannot: that count is not in the tree.
-- =====================================================================

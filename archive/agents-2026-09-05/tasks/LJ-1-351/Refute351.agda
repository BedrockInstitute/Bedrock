{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.351] `graphWitK` IS FALSE, AND ITS PREMISE IS INHABITED.
--
-- `[LJ-1.348]` marked `graphWitK` INFERRED false and built no term.
-- `[LJ-1.349]`, the adversarial review, ruled that the verdict must be
-- MEASURED, because only ONE of the FIVE premise conjuncts had been
-- inhabited.  This file inhabits all five and refutes the conclusion.
--
-- THE TIE, verbatim from src/L/Condensation.lagda.md:7288-7297.  It is
-- the outer name of `SatGraphAgree`'s own `witK` parameter, declared at
-- :7009-7018 and wired at :7319-7321.  `module SatGraphAgree` is at
-- :6961.  Every line number here was re-derived today (C-44).
--
--   (graphWitK : (d e f : S) -> < (f :: e :: d :: g) |=
--                (var zero = var (6 + w))
--                /\ (closedAt 2
--                  /\ (domAt 1 2
--                    /\ (appAt 1 4 3
--                      /\ twelveAt 2 1 0)))>
--           -> < fst d in K > x < fst e in K > x < fst f in K >)
--
-- THE COUNTERMODEL is a ONE-ENTRY SATISFACTION TABLE, and it is
-- CORRECT mathematics, not a dodge.  The code set holds ONE code, the
-- code of the constant `bot` at an arity the tie never bounds.  The
-- table gives that code the value `empty`, which is the true value of
-- `bot`.  So:
--
--   * `closedAt` is satisfied because tag 7 is not one of the eight
--     tags `closedAt` speaks about (src/L/Coding/Model.lagda.md:2181-
--     2188: tags 2, 3, 4, 5, 8, 9, 10, 11);
--   * ELEVEN of the twelve clauses are satisfied for the same reason;
--   * the TWELFTH, `botClauseAt` at tag 7
--     (src/L/Coding/Model.lagda.md:1281-1282), is satisfied by a REAL
--     term: the value is empty, which is what the clause demands;
--   * `domAt` holds because the table's domain is exactly the code set;
--   * `appAt` holds because the two free slots are that code and that
--     value.
--
-- THE CHAPTER ITSELF PREDICTS THIS.  src/L/Coding/Graph.lagda.md:71-72
-- says 「a table with one entry at a compound code satisfies all
-- twelve, so closedness and totality are not decoration」.  This file
-- measures that closedness and totality are NOT ENOUGH either.
--
-- THE ARITY SLOT IS WHERE THE COUNTERMODEL ENTERS, and that is
-- `[LJ-1.350]`'s finding at a different tie: no closure predicate says
-- one word about the arity component.  Here the arity is the BOUND
-- ITSELF, so the conclusion `d in K` gives `K in K`.
--
-- THE CONTROL IS ONE ARGUMENT APART.  `module Point` takes the arity
-- as its only argument.  At `arg = numeralL 0` the premise is
-- inhabited AND the first conclusion HOLDS.  At `arg = K` the premise
-- is inhabited AND the first conclusion is REFUTED.
--
-- EVERY ambient fact comes from the chapter's own delivered public
-- code: `ChainZ` at src/L/Condensation.lagda.md:2820-2844 and `KTies`
-- at :6227-6234.  This file re-writes no pair lemma.
--
-- ONE agda process under GHCRTS="-A64m -I0 -M8g".

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( var; _≐_; _∧̇_; ⊥̇ )

open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆; ∅; ∅-empty ) renaming ( module InfinitySet to Inf )
open Inf using ( #_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ∈∈ₛ )
open import Cubical.Data.Nat using ( ℕ; _+_ )
open import Cubical.Data.Nat.Order using ( _<_; ¬m<m )
open import Cubical.Data.Sigma using ( _×_ )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

module LJ-1-351.Refute351 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import V.Coding {ℓ} using ( pr; pr-inj; #-inj )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL-trans; IsOrd; Lset )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )

import L.Coding.Model
module GM = L.Coding.Model {ℓ}
open GM using ( prʟ; prʟ-fst; closedAt; domAt; appAt; appAt-adequate
              ; domAt-intro; emptyAt; extAt-in-both
              ; binSameClosed-in; unSameClosed-in
              ; unSuccClosed-in; binSuccClosed-in
              ; binClause-in; unClause-in )
open GM.AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

open import L.Coding.Graph {ℓ} lem using ( twelveAt )
open import L.Coding.CodeSet {ℓ} lem using ( arityNumAtL; arityNumAtL-in )

open import L.Condensation {ℓ} lem
  using ( module KFactsNS; module ChainZ; module KTies; module KValue )
open KFactsNS

open import LJ-1-347.Elim347 {ℓ} using ( x∈pair; pair-only )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )

-- =====================================================================
-- PART 0.  THE TAG ARITHMETIC.
--
-- Tag 7 is not tag k, for the eleven other tags.  ONE helper and two
-- orderings.  C-58: no pattern match of mine splits a numeral index.
-- =====================================================================

private
  lo : (k : ℕ) → k < 7 → 7 ≡ k → Empty.⊥
  lo k lt e = ¬m<m (subst (k <_) e lt)

  hi : (k : ℕ) → 7 < k → 7 ≡ k → Empty.⊥
  hi k lt e = ¬m<m (subst (_< k) e lt)

-- =====================================================================
-- PART 1.  THE FRAME.
--
-- The six parameters are `KFacts` fields and nothing else.  `w` is the
-- carrier slot and `K` the bound slot, exactly as in the chapter.
-- =====================================================================

module Refute {n : ℕ} (w K : Fin n) (γ : S ^ n)
  (numK0 : ⟨ fst (numeralL 0) ∈ fst (lookup K γ) ⟩)
  (numK7 : ⟨ fst (numeralL 7) ∈ fst (lookup K γ) ⟩)
  (pairK : (a b : S) → ⟨ fst a ∈ fst (lookup K γ) ⟩
         → ⟨ fst b ∈ fst (lookup K γ) ⟩
         → ⟨ fst (prʟ a b) ∈ fst (lookup K γ) ⟩)
  (carrierK : (v : S) → ⟨ fst v ∈ fst (lookup w γ) ⟩
            → ⟨ fst v ∈ fst (lookup K γ) ⟩)
  (arityK : (N v : S) → ⟨ fst v ∈ fst N ⟩ → ⟨ fst N ∈ fst (lookup K γ) ⟩
          → ⟨ fst v ∈ fst (lookup K γ) ⟩) where

  -- THE CHAPTER'S OWN AMBIENT PAIR FACTS, at :2820-2844.  PUBLIC.
  -- Six probes have now re-written those four lines; this one does not.
  module Z = ChainZ {n} K γ arityK

  -- THE CHAPTER'S OWN SINGLETON CLOSURE, at :6227-6234.  PUBLIC.
  open KTies w K γ numK0 pairK carrierK arityK using ( sgltK )

  private
    bnd : V ℓ
    bnd = fst (lookup K γ)

  -- The unordered pair as an element of the model.  Its `isL` proof is
  -- one `isL-trans` under the chapter's `pair∈pr`.
  pairS : S → S → S
  pairS a b = ⁅ fst a , fst b ⁆
            , isL-trans {x = fst (prʟ a b)} {y = ⁅ fst a , fst b ⁆}
                (subst (λ v → ⟨ ⁅ fst a , fst b ⁆ ∈ v ⟩) (sym (prʟ-fst a b))
                  (Z.pair∈pr (fst a) (fst b)))
                (snd (prʟ a b))

  sglS : S → S
  sglS a = pairS a a

  sglK : (a : S) → ⟨ fst a ∈ bnd ⟩ → ⟨ fst (sglS a) ∈ bnd ⟩
  sglK a ha = sgltK a (sglS a) refl ha

  -- ===================================================================
  -- PART 2.  THE POINT.  ONE ARGUMENT: THE CODE'S ARITY.
  -- ===================================================================

  -- FROM A PAIR IN THE BOUND, ITS TWO HALVES.  Two `arityK` steps
  -- each, both on the chapter's own `ChainZ`.
  private
    pairIn : (u v : S) → ⟨ fst (pairS u v) ∈ fst (prʟ u v) ⟩
    pairIn u v = subst (λ t → ⟨ ⁅ fst u , fst v ⁆ ∈ t ⟩)
                   (sym (prʟ-fst u v)) (Z.pair∈pr (fst u) (fst v))

    prFst : (u v : S) → ⟨ fst (prʟ u v) ∈ bnd ⟩ → ⟨ fst u ∈ bnd ⟩
    prFst u v h = arityK (pairS u v) u (x∈pair (fst u) (fst v))
                    (arityK (prʟ u v) (pairS u v) (pairIn u v) h)

    prSnd : (u v : S) → ⟨ fst (prʟ u v) ∈ bnd ⟩ → ⟨ fst v ∈ bnd ⟩
    prSnd u v h = arityK (pairS u v) v (Z.b∈pair (fst u) (fst v))
                    (arityK (prʟ u v) (pairS u v) (pairIn u v) h)

  module Point (arg payS : S) where

    yS : S
    yS = numeralL 0

    -- The payload of a constant code is a numeral in the intended
    -- reading, and the frame does not care what it is.
    tailS : S
    tailS = prʟ (numeralL 7) payS

    -- THE CODE OF `bot`, AT ARITY `arg` AND PAYLOAD `payS`.  Tag 7.
    cS : S
    cS = prʟ arg tailS

    codeEq : fst cS ≡ pr (fst arg) (pr (# 7) (fst payS))
    codeEq = prʟ-fst arg tailS
      ∙ cong (pr (fst arg))
          (prʟ-fst (numeralL 7) payS
            ∙ cong (λ v → pr v (fst payS)) (numeralL-fst 7))

    -- THE CODE SET, THE ENTRY, AND THE TABLE.
    dS : S
    dS = sglS cS

    entryS : S
    entryS = prʟ cS yS

    eS : S
    eS = sglS entryS

    -- THE ENVIRONMENT.  Slot 0 is the `y` argument, slot 1 the `x`
    -- argument, slot 2 a spacer, and everything past that is the
    -- chapter's own `γ`, so `lookup (suc (suc (suc K))) γ⁺` IS
    -- `lookup K γ`.
    γ⁺ : S ^ (3 + n)
    γ⁺ = yS ∷ cS ∷ yS ∷ γ

    fS : S
    fS = lookup w γ

    E : S ^ (6 + n)
    E = fS ∷ eS ∷ dS ∷ γ⁺

    -- =================================================================
    -- PART 3.  THE PREMISE, ALL FIVE CONJUNCTS.
    -- =================================================================

    -- Membership in the code set pins the code.
    inD : (c : S) → ⟨ fst c ∈ fst dS ⟩ → fst c ≡ fst cS
    inD c h = pair-only (fst cS) (fst c) h

    cS∈dS : ⟨ fst cS ∈ fst dS ⟩
    cS∈dS = x∈pair (fst cS) (fst cS)

    -- THE ONE REFUSAL, SHARED BY NINETEEN CLAUSES.  A member of the
    -- code set is the tag-7 code, and tag 7 is not tag k.
    bad : (k : ℕ) → (7 ≡ k → Empty.⊥) → (c ar : S) (tail : V ℓ)
        → ⟨ fst c ∈ fst dS ⟩
        → fst c ≡ pr (fst ar) (pr (# k) tail)
        → Empty.⊥
    bad k ne c ar tail c∈ sh = ne (#-inj 7 k
      (pr-inj (pr-inj (sym codeEq ∙ sym (inD c c∈) ∙ sh) .snd) .fst))

    -- CONJUNCT 2.  `closedAt` on the code set.  Its eight clauses stand
    -- at tags 2, 3, 4, 5, 8, 9, 10 and 11.
    closed : ⟨ E ⊨ closedAt (suc (suc zero)) ⟩
    closed =
        binSameClosed-in (suc (suc zero)) 2 E
          (λ c ar a b c∈ sh → Empty.rec (bad 2 (lo 2 (4 , refl)) c ar _ c∈ sh))
      , ( binSameClosed-in (suc (suc zero)) 3 E
            (λ c ar a b c∈ sh → Empty.rec (bad 3 (lo 3 (3 , refl)) c ar _ c∈ sh))
      , ( binSameClosed-in (suc (suc zero)) 4 E
            (λ c ar a b c∈ sh → Empty.rec (bad 4 (lo 4 (2 , refl)) c ar _ c∈ sh))
      , ( unSameClosed-in (suc (suc zero)) 5 E
            (λ c ar a c∈ sh → Empty.rec (bad 5 (lo 5 (1 , refl)) c ar _ c∈ sh))
      , ( unSuccClosed-in (suc (suc zero)) 8 E
            (λ c ar a c∈ sh → Empty.rec (bad 8 (hi 8 (0 , refl)) c ar _ c∈ sh))
      , ( unSuccClosed-in (suc (suc zero)) 9 E
            (λ c ar a c∈ sh → Empty.rec (bad 9 (hi 9 (1 , refl)) c ar _ c∈ sh))
      , ( binSuccClosed-in (suc (suc zero)) 10 E
            (λ c ar a b c∈ sh → Empty.rec (bad 10 (hi 10 (2 , refl)) c ar _ c∈ sh))
      ,   binSuccClosed-in (suc (suc zero)) 11 E
            (λ c ar a b c∈ sh → Empty.rec (bad 11 (hi 11 (3 , refl)) c ar _ c∈ sh))
        ))))))

    -- CONJUNCT 4.  The table holds the pair of the two free slots.
    entry∈eS : ⟨ pr (fst cS) (fst yS) ∈ fst eS ⟩
    entry∈eS = subst (λ v → ⟨ v ∈ fst eS ⟩) (prʟ-fst cS yS)
                 (x∈pair (fst entryS) (fst entryS))

    app : ⟨ E ⊨ appAt (suc zero) (suc (suc (suc (suc zero))))
                       (suc (suc (suc zero))) ⟩
    app = subst ⟨_⟩
      (sym (appAt-adequate (suc zero) (suc (suc (suc (suc zero))))
              (suc (suc (suc zero))) E))
      entry∈eS

    -- Membership in the table pins the entry.
    inE : (v : S) (y : S) → ⟨ pr (fst v) (fst y) ∈ fst eS ⟩
        → (fst v ≡ fst cS) × (fst y ≡ fst yS)
    inE v y h = pr-inj (pair-only (fst entryS) (pr (fst v) (fst y)) h
                        ∙ prʟ-fst cS yS)

    -- CONJUNCT 3.  The code set IS the domain of the table.
    dom : ⟨ E ⊨ domAt (suc zero) (suc (suc zero)) ⟩
    dom = domAt-intro (suc zero) (suc (suc zero)) E
      (λ x
        → PT.rec (snd (fst x ∈ fst dS))
            (λ { (y , h) → subst (λ v → ⟨ v ∈ fst dS ⟩)
                             (sym (inE x y h .fst)) cS∈dS })
        , (λ h → ∣ yS , subst (λ v → ⟨ pr v (fst yS) ∈ fst eS ⟩)
                          (sym (inD x h)) entry∈eS ∣₁))
    -- CONJUNCT 5, CLAUSE 8 OF 12.  THE ONLY CLAUSE THAT IS NOT VACUOUS.
    -- The value at the code of `bot` must be empty, and it IS empty.
    botC : ⟨ E ⊨ GM.botClauseAt (suc (suc zero)) (suc zero) ⟩
    botC = GM.botClause-in (suc (suc zero)) (suc zero) E
      (λ c ar a yc c∈ sh hc →
        extAt-in-both zero ⊥̇ (yc ∷ a ∷ ar ∷ c ∷ E)
          (λ z hz → Empty.rec
            (∅-empty (fst z) (∈∈ₛ {a = fst z} {b = ∅} .fst
              (subst (λ v → ⟨ fst z ∈ v ⟩)
                (inE c yc hc .snd ∙ numeralL-fst 0) hz))))
          (λ z hz → Empty.rec* hz))

    -- CONJUNCT 5.  THE TWELVE.  Eleven refusals and the term above.
    twelve : ⟨ E ⊨ twelveAt (suc (suc zero)) (suc zero) zero ⟩
    twelve =
        binClause-in (suc (suc zero)) (suc zero) 0
          (GM.atomRel zero GM.memRel) E
          (λ c ar a b yc c∈ sh hc →
            Empty.rec (bad 0 (lo 0 (6 , refl)) c ar _ c∈ sh))
      , ( binClause-in (suc (suc zero)) (suc zero) 1
            (GM.atomRel zero GM.eqRel) E
            (λ c ar a b yc c∈ sh hc →
              Empty.rec (bad 1 (lo 1 (5 , refl)) c ar _ c∈ sh))
      , ( binClause-in (suc (suc zero)) (suc zero) 2
            (GM.propRel (suc zero)
              (GM.interAt (suc (suc zero)) (suc zero) zero)) E
            (λ c ar a b yc c∈ sh hc →
              Empty.rec (bad 2 (lo 2 (4 , refl)) c ar _ c∈ sh))
      , ( binClause-in (suc (suc zero)) (suc zero) 3
            (GM.propRel (suc zero)
              (GM.unionAt (suc (suc zero)) (suc zero) zero)) E
            (λ c ar a b yc c∈ sh hc →
              Empty.rec (bad 3 (lo 3 (3 , refl)) c ar _ c∈ sh))
      , ( GM.impClause-in (suc (suc zero)) (suc zero) zero E
            (λ c ar a b yc ya yb EE c∈ sh hc ha hb hE →
              Empty.rec (bad 4 (lo 4 (2 , refl)) c ar _ c∈ sh))
      , ( GM.negClause-in (suc (suc zero)) (suc zero) zero E
            (λ c ar a yc ya EE c∈ sh hc ha hE →
              Empty.rec (bad 5 (lo 5 (1 , refl)) c ar _ c∈ sh))
      , ( GM.topClause-in (suc (suc zero)) (suc zero) zero E
            (λ c ar a yc EE c∈ sh hc hE →
              Empty.rec (bad 6 (lo 6 (0 , refl)) c ar _ c∈ sh))
      , ( botC
      , ( unClause-in (suc (suc zero)) (suc zero) 8
            (GM.quantRel (suc zero) zero (GM.body∃ zero)) E
            (λ c ar a yc c∈ sh hc →
              Empty.rec (bad 8 (hi 8 (0 , refl)) c ar _ c∈ sh))
      , ( unClause-in (suc (suc zero)) (suc zero) 9
            (GM.quantRel (suc zero) zero (GM.body∀ zero)) E
            (λ c ar a yc c∈ sh hc →
              Empty.rec (bad 9 (hi 9 (1 , refl)) c ar _ c∈ sh))
      , ( binClause-in (suc (suc zero)) (suc zero) 10
            (GM.bndRel (suc zero) zero (GM.bodyAll zero)) E
            (λ c ar a b yc c∈ sh hc →
              Empty.rec (bad 10 (hi 10 (2 , refl)) c ar _ c∈ sh))
      ,   binClause-in (suc (suc zero)) (suc zero) 11
            (GM.bndRel (suc zero) zero (GM.bodyEx zero)) E
            (λ c ar a b yc c∈ sh hc →
              Empty.rec (bad 11 (hi 11 (3 , refl)) c ar _ c∈ sh))
        ))))))))))

    -- CONJUNCT 1.  The carrier slot, taken as itself.
    pin : ⟨ E ⊨ (var zero ≐ var (suc (suc (suc (suc (suc (suc w))))))) ⟩
    pin = refl

    -- THE PREMISE, WHOLE.  A CLOSED TERM.  This is what `[LJ-1.349]`
    -- ruled must exist before the verdict is believed.
    premise : ⟨ E ⊨ (var zero ≐ var (suc (suc (suc (suc (suc (suc w)))))))
                 ∧̇ (closedAt (suc (suc zero))
                   ∧̇ (domAt (suc zero) (suc (suc zero))
                     ∧̇ (appAt (suc zero) (suc (suc (suc (suc zero))))
                              (suc (suc (suc zero)))
                       ∧̇ twelveAt (suc (suc zero)) (suc zero) zero))) ⟩
    premise = pin , (closed , (dom , (app , twelve)))

    -- THE TIE, verbatim from src/L/Condensation.lagda.md:7288-7297.
    GraphWitK : Type (ℓ-suc ℓ)
    GraphWitK = (d e f : S)
      → ⟨ (f ∷ e ∷ d ∷ γ⁺) ⊨
          (var zero ≐ var (suc (suc (suc (suc (suc (suc w)))))))
          ∧̇ (closedAt (suc (suc zero))
            ∧̇ (domAt (suc zero) (suc (suc zero))
              ∧̇ (appAt (suc zero) (suc (suc (suc (suc zero))))
                       (suc (suc (suc zero)))
                ∧̇ twelveAt (suc (suc zero)) (suc zero) zero))) ⟩
      → ⟨ fst d ∈ fst (lookup (suc (suc (suc K))) γ⁺) ⟩
        × ⟨ fst e ∈ fst (lookup (suc (suc (suc K))) γ⁺) ⟩
        × ⟨ fst f ∈ fst (lookup (suc (suc (suc K))) γ⁺) ⟩

    -- The tie's FIRST conclusion at this point.
    firstConcl : GraphWitK → ⟨ fst dS ∈ bnd ⟩
    firstConcl h = h dS eS fS premise .fst

  -- ===================================================================
  -- PART 4.  THE REFUTATION.  ARITY := THE BOUND ITSELF.
  -- ===================================================================

  private
    Kv : S
    Kv = lookup K γ

  -- POINT ONE.  The ARITY is the bound.  This is `[LJ-1.350]`'s free
  -- slot, at a different tie.
  module Bad1 = Point Kv (numeralL 0)

  -- POINT TWO.  The arity is a GENUINE NUMERAL and the PAYLOAD is the
  -- bound.  `arityNumAtL`, the bound `[LJ-1.350]` found delivered,
  -- HOLDS at this code, and the tie is STILL false.
  module Bad2 = Point (numeralL 0) Kv

  -- `graphWitK` IS FALSE.  MEASURED.
  graphWitK-false : Bad1.GraphWitK → Empty.⊥
  graphWitK-false h = ∈-irrefl bnd
    (prFst Kv Bad1.tailS
      (arityK Bad1.dS Bad1.cS Bad1.cS∈dS (Bad1.firstConcl h)))

  -- AND IT IS FALSE AT A CODE WHOSE ARITY IS A NUMERAL.  MEASURED.
  graphWitK-false-num : Bad2.GraphWitK → Empty.⊥
  graphWitK-false-num h = ∈-irrefl bnd
    (prSnd (numeralL 7) Kv
      (prSnd (numeralL 0) Bad2.tailS
        (arityK Bad2.dS Bad2.cS Bad2.cS∈dS (Bad2.firstConcl h))))

  -- THE DELIVERED BOUND HOLDS AT THE SECOND COUNTERMODEL'S CODE.
  -- `arityNumAtL` is `src/L/Coding/CodeSet.lagda.md:185-188` and
  -- `arityNumAtL-in` is `:201-207`.  So the bound that closed a sibling
  -- tie does NOT close this one.  MEASURED, by this term.
  bad2-arityNum : ⟨ Bad2.γ⁺ ⊨ arityNumAtL (suc zero) ⟩
  bad2-arityNum = arityNumAtL-in (suc zero) Bad2.γ⁺ 0 Bad2.tailS
    (prʟ-fst (numeralL 0) Bad2.tailS
      ∙ cong (λ v → pr v (fst Bad2.tailS)) (numeralL-fst 0))

  -- ===================================================================
  -- PART 5.  THE NEGATIVE CONTROL, ONE ARGUMENT APART.
  --
  -- The SAME conclusion, at the SAME frame, with ONE argument changed:
  -- the arity is `numeralL 0` instead of the bound.  The premise is
  -- still inhabited, and now the conclusion HOLDS.  So the refutation
  -- measures the SITE and not the statement (C-42), and the tie's
  -- premise class is NOT empty (the point of this task).
  -- ===================================================================

  module Good = Point (numeralL 0) (numeralL 0)

  good-premise : ⟨ Good.E ⊨
      (var zero ≐ var (suc (suc (suc (suc (suc (suc w)))))))
      ∧̇ (closedAt (suc (suc zero))
        ∧̇ (domAt (suc zero) (suc (suc zero))
          ∧̇ (appAt (suc zero) (suc (suc (suc (suc zero))))
                   (suc (suc (suc zero)))
            ∧̇ twelveAt (suc (suc zero)) (suc zero) zero))) ⟩
  good-premise = Good.premise

  good-code∈K : ⟨ fst Good.cS ∈ bnd ⟩
  good-code∈K = pairK (numeralL 0) (prʟ (numeralL 7) (numeralL 0)) numK0
                  (pairK (numeralL 7) (numeralL 0) numK7 numK0)

  -- THE FIRST CONCLUSION HOLDS AT THE GOOD ARITY.
  good-first : ⟨ fst Good.dS ∈ bnd ⟩
  good-first = sglK Good.cS good-code∈K

  -- AND SO DOES THE SECOND.
  good-second : ⟨ fst Good.eS ∈ bnd ⟩
  good-second = sglK Good.entryS
                  (pairK Good.cS (numeralL 0) good-code∈K numK0)

-- =====================================================================
-- PART 6.  NON-VACUITY AT THE DELIVERED RECORD.
--
-- `module KValue` (src/L/Condensation.lagda.md:7380) builds the ONE
-- `KFacts` value the chapter has.  The refutation runs on THAT record,
-- so this is not a parameters-green (C-45): the five closure facts
-- arrive from the chapter and nothing here restates one.
--
-- NO extra hypothesis is needed.  The countermodel never asks the
-- carrier for a member, so `[LJ-1.350]`'s `#1∈γ` has no counterpart
-- here.
-- =====================================================================

module Wire (lam : V ℓ) (ordλ : IsOrd lam)
            (succλ : (d : V ℓ) → ⟨ d ∈ lam ⟩ → ⟨ Inf.sucV d ∈ lam ⟩)
            (∅∈λ : ⟨ ∅ ∈ lam ⟩)
            (gam : V ℓ) (ordγ : IsOrd gam) (γ∈λ : ⟨ gam ∈ lam ⟩) where

  module KV = KValue lam ordλ succλ ∅∈λ gam ordγ γ∈λ

  open KFacts KV.facts using ( numK0; numK7; pairK; carrierK; arityK )

  module R = Refute KV.iA KV.iK KV.Kenv numK0 numK7 pairK carrierK arityK

  -- `graphWitK` IS FALSE AT THE DELIVERED RECORD.
  live-false : R.Bad1.GraphWitK → Empty.⊥
  live-false = R.graphWitK-false

  live-false-num : R.Bad2.GraphWitK → Empty.⊥
  live-false-num = R.graphWitK-false-num

  -- AND THE PREMISE IS INHABITED THERE, AT BOTH ARGUMENTS.
  live-bad-premise : ⟨ R.Bad1.E ⊨
      (var zero ≐ var (suc (suc (suc (suc (suc (suc KV.iA)))))))
      ∧̇ (closedAt (suc (suc zero))
        ∧̇ (domAt (suc zero) (suc (suc zero))
          ∧̇ (appAt (suc zero) (suc (suc (suc (suc zero))))
                   (suc (suc (suc zero)))
            ∧̇ twelveAt (suc (suc zero)) (suc zero) zero))) ⟩
  live-bad-premise = R.Bad1.premise

  live-good : ⟨ fst R.Good.dS ∈ Lset lam ⟩
  live-good = R.good-first

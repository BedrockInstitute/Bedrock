{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.350] SHAPEDNESS IS NOT THE MISSING BOUND.  MEASURED.
--
-- `[LJ-1.347]` section 6 proposes to repair the 24 third-shape ties by
-- adding SHAPEDNESS to the container, and prices the sweep at about 280
-- insertions.  `[LJ-1.348]` section 2 measured that `shapedAt` leaves
-- the ARITY slot free.  The two readings are not compatible.  This file
-- decides between them, at ONE tie, with a countermodel.
--
-- THE TIE, verbatim from src/L/Condensation.lagda.md:6268-6273
-- (`module ShapesAgree`, third shape, sub-family A, container a bare
-- `C : S`):
--
--   (compK : (k : N) (c N a b : S) -> < fst c in fst C >
--           -> fst c = pr (fst N) (pr (# k) (pr (fst a) (fst b)))
--           -> < fst N in K > x < fst a in K > x < fst b in K >
--           x || Sigma[ n in N ] (fst N = # n) ||)
--
-- THE REPAIR UNDER TEST adds the shapedness of the container.  It is
-- given here in its STRONGEST form, per member: `ShapeWit A g c`, which
-- is what `shaped-out` (src/L/Coding/Shape.lagda.md:242) delivers from
-- `< g |= shapedAt C A >` at each member.  A refutation of the strong
-- form refutes the weak form too.
--
-- THE COUNTERMODEL puts a NON-NUMERAL in the arity slot of a TAG 2
-- code.  Tag 2 carries `noneB`, which is `TOP`
-- (src/L/Coding/Shape.lagda.md:175-176), so the shape says nothing at
-- all about the three components.  `Cset-shaped` proves EVERY member of
-- the container is a shape, which is the exact input `shaped-in`
-- (:326-328) asks for.
--
-- EVERY ambient fact comes from the chapter's own delivered code:
-- `ChainZ` at src/L/Condensation.lagda.md:2837-2844 and `KTies` at
-- :6227-6234, both PUBLIC.  This file re-writes no private lemma and
-- adds no closure fact.  It does NOT import
-- agents/tasks/LJ-1-344/Supply344.agda, which is RED today.
--
-- ONE agda process under GHCRTS="-A64m -I0 -M8g".

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

open import FOL.ZFStructure using ( module hPropStructure )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆; ∅ ) renaming ( module InfinitySet to Inf )
open Inf using ( #_; sucV )
open import Cubical.Data.Nat using ( ℕ )
open import Cubical.Data.Sigma using ( _×_ )
open import Cubical.Data.Sum using ( inl; inr )
open import Cubical.Data.Unit using ( tt* )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

module LJ-1-350.Refute350 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL-trans; IsOrd; Lset; Lset-mono )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )
open import L.Ordinal {ℓ} using ( numeral-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )

import L.Coding.Model
module GM = L.Coding.Model {ℓ}
open GM using ( prʟ; prʟ-fst )
open GM.AbsL using ( _^_ )

open import L.Coding.Shape {ℓ} using ( ShapeWit )

open import L.Condensation {ℓ} lem
  using ( module KFactsNS; module ChainZ; module KTies; module KValue )
open KFactsNS

open import LJ-1-347.Elim347 {ℓ} using ( sgl1-not-numeral; pair-only )

open hPropStructure 𝒮ʟ using ( S )

-- =====================================================================
-- PART 1.  THE REFUTATION OF THE REPAIRED TIE.
--
-- The five closure parameters are `KFacts` fields and nothing else.
-- `u` and `hu` say the carrier slot has a MEMBER.  Without them the
-- refutation would be empty and would say nothing about the delivered
-- setting (C-45).
-- =====================================================================

module Refute {n : ℕ} (A K : Fin n) (γ : S ^ n)
  (numK0 : ⟨ fst (numeralL 0) ∈ fst (lookup K γ) ⟩)
  (numK1 : ⟨ fst (numeralL 1) ∈ fst (lookup K γ) ⟩)
  (numK2 : ⟨ fst (numeralL 2) ∈ fst (lookup K γ) ⟩)
  (pairK : (a b : S) → ⟨ fst a ∈ fst (lookup K γ) ⟩
         → ⟨ fst b ∈ fst (lookup K γ) ⟩
         → ⟨ fst (prʟ a b) ∈ fst (lookup K γ) ⟩)
  (carrierK : (v : S) → ⟨ fst v ∈ fst (lookup A γ) ⟩
            → ⟨ fst v ∈ fst (lookup K γ) ⟩)
  (arityK : (N v : S) → ⟨ fst v ∈ fst N ⟩ → ⟨ fst N ∈ fst (lookup K γ) ⟩
          → ⟨ fst v ∈ fst (lookup K γ) ⟩) where

  -- THE CHAPTER'S OWN AMBIENT PAIR FACTS, at :2837-2844.  PUBLIC.
  -- Five probes re-wrote these four lines; this one does not.
  module Z = ChainZ {n} K γ arityK

  -- THE CHAPTER'S OWN SINGLETON CLOSURE, at :6227-6234.
  open KTies A K γ numK0 pairK carrierK arityK using ( sgltK )

  private
    bnd : V ℓ
    bnd = fst (lookup K γ)

  sglS : S → S
  sglS a = ⁅ fst a , fst a ⁆
         , isL-trans {x = fst (prʟ a a)} {y = ⁅ fst a , fst a ⁆}
             (subst (λ v → ⟨ ⁅ fst a , fst a ⁆ ∈ v ⟩) (sym (prʟ-fst a a))
               (Z.pair∈pr (fst a) (fst a)))
             (snd (prʟ a a))

  sglK : (a : S) → ⟨ fst a ∈ bnd ⟩ → ⟨ fst (sglS a) ∈ bnd ⟩
  sglK a ha = sgltK a (sglS a) refl ha

  module Point (u : S) (hu : ⟨ fst u ∈ fst (lookup A γ) ⟩) where

    -- THE ARITY SLOT.  Its set is the singleton of the numeral one,
    -- which `Elim347.agda` refutes as a numeral at EVERY index.
    arS : S
    arS = sglS (numeralL 1)

    ar-fst : fst arS ≡ ⁅ # 1 , # 1 ⁆
    ar-fst = cong (λ w → ⁅ w , w ⁆) (numeralL-fst 1)

    arS∈K : ⟨ fst arS ∈ bnd ⟩
    arS∈K = sglK (numeralL 1) numK1

    uK : ⟨ fst u ∈ bnd ⟩
    uK = carrierK u hu

    -- THE CODE, at TAG 2, whose shape relation is `noneB` = TOP.
    cS : S
    cS = prʟ arS (prʟ (numeralL 2) (prʟ u u))

    codeEq : fst cS ≡ pr (fst arS) (pr (# 2) (pr (fst u) (fst u)))
    codeEq = prʟ-fst arS (prʟ (numeralL 2) (prʟ u u))
      ∙ cong (pr (fst arS))
          (prʟ-fst (numeralL 2) (prʟ u u)
            ∙ cong₂ pr (numeralL-fst 2) (prʟ-fst u u))

    cS∈K : ⟨ fst cS ∈ bnd ⟩
    cS∈K = pairK arS (prʟ (numeralL 2) (prʟ u u)) arS∈K
             (pairK (numeralL 2) (prʟ u u) numK2 (pairK u u uK uK))

    -- THE CONTAINER.  The singleton of the code, and in the bound.
    Cset : S
    Cset = sglS cS

    Cset∈K : ⟨ fst Cset ∈ bnd ⟩
    Cset∈K = sglK cS cS∈K

    cS∈Cset : ⟨ fst cS ∈ fst Cset ⟩
    cS∈Cset = Z.b∈pair (fst cS) (fst cS)

    -- THE CONTAINER IS SHAPED, AT EVERY MEMBER.
    --
    -- This is the exact hypothesis `shaped-in`
    -- (src/L/Coding/Shape.lagda.md:326-328) takes to build
    -- `< g |= shapedAt C A >`.  So the container really does satisfy
    -- shapedness, and the repair `[LJ-1.347]` proposes really is
    -- available here.  Tag 2 is the third disjunct, and its relation
    -- `noneB` is TOP, so the witness is one `tt*`.
    Cset-shaped : (c : S) → ⟨ fst c ∈ fst Cset ⟩ → ∥ ShapeWit A γ c ∥₁
    Cset-shaped c hc = ∣ inr (inr (inl (arS , (u , (u , (eq , tt*)))))) ∣₁
      where
      eq : fst c ≡ pr (fst arS) (pr (# 2) (pr (fst u) (fst u)))
      eq = pair-only (fst cS) (fst c) hc ∙ codeEq

    -- THE REPAIRED TIE.  `[LJ-1.347]`'s cure, stated at
    -- src/L/Condensation.lagda.md:6268-6273 with the shapedness of the
    -- container ADDED as its fourth argument.
    CompK⁺ : Type (ℓ-suc ℓ)
    CompK⁺ = (k : ℕ) (c N a b : S) → ⟨ fst c ∈ fst Cset ⟩
           → ∥ ShapeWit A γ c ∥₁
           → fst c ≡ pr (fst N) (pr (# k) (pr (fst a) (fst b)))
           → ⟨ fst N ∈ bnd ⟩ × ⟨ fst a ∈ bnd ⟩ × ⟨ fst b ∈ bnd ⟩
             × ∥ Σ[ m ∈ ℕ ] (fst N ≡ # m) ∥₁

    -- NON-VACUITY, LAYER ONE.  The three OTHER conclusions of the tie
    -- are TRUE at these witnesses.  The repaired tie dies at a point
    -- where every other conjunct holds, and ONLY the arity conjunct is
    -- refuted (C-42).
    other-conjuncts : ⟨ fst arS ∈ bnd ⟩ × ⟨ fst u ∈ bnd ⟩ × ⟨ fst u ∈ bnd ⟩
    other-conjuncts = arS∈K , uK , uK

    -- NON-VACUITY, LAYER TWO.  Every premise the repaired tie asks for
    -- is a CLOSED term here, built and never assumed: `cS∈Cset`,
    -- `Cset-shaped` and `codeEq` above.

    -- THE REFUTATION.  SHAPEDNESS DOES NOT SAVE THE TIE.
    compK⁺-false : CompK⁺ → Empty.⊥
    compK⁺-false h = PT.rec Empty.isProp⊥
      (λ { (m , q) → sgl1-not-numeral m (sym ar-fst ∙ q) })
      (h 2 cS arS u u cS∈Cset (Cset-shaped cS cS∈Cset) codeEq
         .snd .snd .snd)

    -- =================================================================
    -- THE NEGATIVE CONTROL, BOTH HALVES, ONE ARGUMENT APART.
    --
    -- The conjunct the refutation kills is SATISFIABLE.  It holds at a
    -- genuine numeral arity and fails at the singleton of that same
    -- numeral.  So the refutation measures the SITE and not the
    -- statement (C-42), and it cannot be pointed at a real code.
    -- =================================================================

    arity-holds : ∥ Σ[ m ∈ ℕ ] (fst (numeralL 1) ≡ # m) ∥₁
    arity-holds = ∣ 1 , numeralL-fst 1 ∣₁

    arity-fails : ∥ Σ[ m ∈ ℕ ] (fst (sglS (numeralL 1)) ≡ # m) ∥₁ → Empty.⊥
    arity-fails = PT.rec Empty.isProp⊥
      (λ { (m , q) → sgl1-not-numeral m (sym ar-fst ∙ q) })

-- =====================================================================
-- PART 2.  NON-VACUITY, LAYER THREE.  AT THE DELIVERED RECORD.
--
-- `module KValue` (src/L/Condensation.lagda.md:7380) builds the ONE
-- `KFacts` value the chapter has.  The refutation runs on THAT record,
-- so this is not a parameters-green: the six closure facts arrive from
-- the chapter and nothing here restates one.
--
-- ONE hypothesis is added, `#1∈γ`, which says the carrier stage is at
-- least 1.  It is what makes the carrier NON-EMPTY.  Without it the tie
-- would be true at this record because nothing would meet it.
-- =====================================================================

module Wire (lam : V ℓ) (ordλ : IsOrd lam)
            (succλ : (d : V ℓ) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩)
            (∅∈λ : ⟨ ∅ ∈ lam ⟩)
            (gam : V ℓ) (ordγ : IsOrd gam) (γ∈λ : ⟨ gam ∈ lam ⟩)
            (#1∈γ : ⟨ (# 1) ∈ gam ⟩) where

  module KV = KValue lam ordλ succλ ∅∈λ gam ordγ γ∈λ

  open KFacts KV.facts using ( numK0; numK1; numK2; pairK; carrierK; arityK )

  module R = Refute KV.iA KV.iK KV.Kenv numK0 numK1 numK2
                    pairK carrierK arityK

  zero∈carrier : ⟨ fst (numeralL 0) ∈ fst (lookup KV.iA KV.Kenv) ⟩
  zero∈carrier = subst (λ u → ⟨ u ∈ Lset gam ⟩) (sym (numeralL-fst 0))
    (Lset-mono {α = gam} {β = # 1} #1∈γ
      {x = # 0} (ord∈Lset-suc (# 0) (numeral-ord 0)))

  module P = R.Point (numeralL 0) zero∈carrier

  -- THE REPAIRED TIE IS FALSE AT THE DELIVERED RECORD.
  repaired-tie-false : P.CompK⁺ → Empty.⊥
  repaired-tie-false = P.compK⁺-false

  -- And its other three conclusions hold there, as closed terms.
  live-other : ⟨ fst P.arS ∈ Lset lam ⟩
             × ⟨ fst (numeralL 0) ∈ Lset lam ⟩
             × ⟨ fst (numeralL 0) ∈ Lset lam ⟩
  live-other = P.other-conjuncts

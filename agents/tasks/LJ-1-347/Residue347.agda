{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.347] THE ARITY NUMERAL CONJUNCT IS FALSE.  MEASURED.
--
-- `[LJ-1.344]` built this countermodel and could not close one clause.
-- It returned INFERRED FALSE and refused to claim more.  `Elim347.agda`
-- closes that clause in 1.64 s.  This file finishes the refutation.
--
-- THE TIE, verbatim from src/L/Condensation.lagda.md:7239-7245:
--
--   (wCodesK : (w' : S) -> < fst w' in K >
--             -> (k : N) -> (c ar a b : S) -> < fst c in fst w' >
--             -> fst c = pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
--             -> < fst ar in K > x < fst a in K > x < fst b in K >
--             x || Sigma[ n in N ] (fst ar = # n) ||)
--
-- THE LAST CONJUNCT SAYS the arity component of a code is a NUMERAL.
-- The premise NEVER says `w'` is a code set.  It says only that `w'` is
-- in the bound and that `c` is a member of `w'`.  `closedAt` and
-- `shapedAt` stand in `witK`'s premise at :7233-7235 and NOT here.  So
-- any set in the bound with any member of the pair shape is legal.
--
-- THE COUNTERMODEL takes `ar` to be the singleton of the numeral one.
-- EVERY ambient fact comes from the chapter's OWN delivered code:
-- `ChainZ` at :2820-2846 and `KTies` at :6197-6259.  This file adds no
-- closure fact and re-writes no private lemma.
--
-- IT DOES NOT IMPORT `agents/tasks/LJ-1-344/Supply344.agda`, which is
-- now RED: `[LJ-1.346]` removed the two tie parameters from
-- `DefinesAgree` (src/L/Condensation.lagda.md:6885-6892) and that file
-- still passes them, MEASURED at `Supply344.agda:292.54-58`.
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
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

module LJ-1-347.Residue347 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

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

open import L.Condensation {ℓ} lem
  using ( module KFactsNS; module ChainZ; module KTies; module KValue )
open KFactsNS

open import LJ-1-347.Elim347 {ℓ} using ( sgl1-not-numeral )

open hPropStructure 𝒮ʟ using ( S )

-- =====================================================================
-- PART 1.  THE REFUTATION.
--
-- The five closure parameters are `KFacts` fields and nothing else.
-- `u` and `hu` say the carrier slot has a MEMBER.  Without them the
-- refutation would be empty and would say nothing about the delivered
-- setting, which is the trap this whole chain is about (C-45).
-- =====================================================================

module Refute {n : ℕ} (A K : Fin n) (γ : S ^ n)
  (numK0 : ⟨ fst (numeralL 0) ∈ fst (lookup K γ) ⟩)
  (numK1 : ⟨ fst (numeralL 1) ∈ fst (lookup K γ) ⟩)
  (pairK : (a b : S) → ⟨ fst a ∈ fst (lookup K γ) ⟩
         → ⟨ fst b ∈ fst (lookup K γ) ⟩
         → ⟨ fst (prʟ a b) ∈ fst (lookup K γ) ⟩)
  (carrierK : (v : S) → ⟨ fst v ∈ fst (lookup A γ) ⟩
            → ⟨ fst v ∈ fst (lookup K γ) ⟩)
  (arityK : (N v : S) → ⟨ fst v ∈ fst N ⟩ → ⟨ fst N ∈ fst (lookup K γ) ⟩
          → ⟨ fst v ∈ fst (lookup K γ) ⟩) where

  -- THE CHAPTER'S OWN AMBIENT PAIR FACTS, at :2837-2844.
  module Z = ChainZ {n} K γ arityK

  -- THE CHAPTER'S OWN SINGLETON CLOSURE, at :6227-6234.
  open KTies A K γ numK0 pairK carrierK arityK using ( sgltK )

  private
    bnd : V ℓ
    bnd = fst (lookup K γ)

  -- The singleton AS A CARRIER ELEMENT.  L is transitive and the pair
  -- is a member of the Kuratowski pair, which `prʟ` already delivers.
  sglS : S → S
  sglS a = ⁅ fst a , fst a ⁆
         , isL-trans {x = fst (prʟ a a)} {y = ⁅ fst a , fst a ⁆}
             (subst (λ v → ⟨ ⁅ fst a , fst a ⁆ ∈ v ⟩) (sym (prʟ-fst a a))
               (Z.pair∈pr (fst a) (fst a)))
             (snd (prʟ a a))

  sglK : (a : S) → ⟨ fst a ∈ bnd ⟩ → ⟨ fst (sglS a) ∈ bnd ⟩
  sglK a ha = sgltK a (sglS a) refl ha

  module Point (u : S) (hu : ⟨ fst u ∈ fst (lookup A γ) ⟩) where

    -- The arity slot.  Its set is the singleton of the numeral one,
    -- which `Elim347.agda` refutes as a numeral at EVERY index.
    arS : S
    arS = sglS (numeralL 1)

    ar-fst : fst arS ≡ ⁅ # 1 , # 1 ⁆
    ar-fst = cong (λ w → ⁅ w , w ⁆) (numeralL-fst 1)

    arS∈K : ⟨ fst arS ∈ bnd ⟩
    arS∈K = sglK (numeralL 1) numK1

    -- The code, of exactly the tie's pair shape, at `k := 0` and
    -- `a := b := u`.
    cS : S
    cS = prʟ arS (prʟ (numeralL 0) (prʟ u u))

    uK : ⟨ fst u ∈ bnd ⟩
    uK = carrierK u hu

    cS∈K : ⟨ fst cS ∈ bnd ⟩
    cS∈K = pairK arS (prʟ (numeralL 0) (prʟ u u)) arS∈K
             (pairK (numeralL 0) (prʟ u u) numK0 (pairK u u uK uK))

    -- The "code set": the singleton of the code.  It is in the bound by
    -- the chapter's own closure, and the code is its member.
    wS : S
    wS = sglS cS

    wS∈K : ⟨ fst wS ∈ bnd ⟩
    wS∈K = sglK cS cS∈K

    cS∈wS : ⟨ fst cS ∈ fst wS ⟩
    cS∈wS = Z.b∈pair (fst cS) (fst cS)

    codeEq : fst cS ≡ pr (fst arS) (pr (# 0) (pr (fst u) (fst u)))
    codeEq = prʟ-fst arS (prʟ (numeralL 0) (prʟ u u))
      ∙ cong (pr (fst arS))
          (prʟ-fst (numeralL 0) (prʟ u u)
            ∙ cong₂ pr (numeralL-fst 0) (prʟ-fst u u))

    -- THE TIE, type VERBATIM from src/L/Condensation.lagda.md:7239-7245.
    WCodesK : Type (ℓ-suc ℓ)
    WCodesK = (w' : S) → ⟨ fst w' ∈ fst (lookup K γ) ⟩
            → (k : ℕ) → (c ar a b : S) → ⟨ fst c ∈ fst w' ⟩
            → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
            → ⟨ fst ar ∈ fst (lookup K γ) ⟩
              × ⟨ fst a ∈ fst (lookup K γ) ⟩
              × ⟨ fst b ∈ fst (lookup K γ) ⟩
            × ∥ Σ[ m ∈ ℕ ] (fst ar ≡ # m) ∥₁

    -- NON-VACUITY, LAYER ONE.  The three OTHER conclusions of the tie
    -- are TRUE at these witnesses.  So the tie dies at a point where
    -- every other conjunct holds, and ONLY the arity conjunct is
    -- refuted.
    other-conjuncts : ⟨ fst arS ∈ bnd ⟩ × ⟨ fst u ∈ bnd ⟩ × ⟨ fst u ∈ bnd ⟩
    other-conjuncts = arS∈K , uK , uK

    -- NON-VACUITY, LAYER TWO.  Every premise the tie asks for is a
    -- CLOSED term here, built and never assumed: `wS∈K`, `cS∈wS` and
    -- `codeEq` above.

    -- THE REFUTATION.
    wCodesK-false : WCodesK → Empty.⊥
    wCodesK-false h = PT.rec Empty.isProp⊥
      (λ { (m , q) → sgl1-not-numeral m (sym ar-fst ∙ q) })
      (h wS wS∈K 0 cS arS u u cS∈wS codeEq .snd .snd .snd)

-- =====================================================================
-- PART 2.  NON-VACUITY, LAYER THREE.  AT THE DELIVERED RECORD.
--
-- `module KValue` (src/L/Condensation.lagda.md:7380) builds the ONE
-- `KFacts` value the chapter has.  The refutation runs on THAT record,
-- so this is not a parameters-green: the five closure facts arrive from
-- the chapter and nothing here restates one.
--
-- ONE hypothesis is added, `#1-in-gam`, which says the carrier stage is
-- at least 1.  It is what makes the carrier NON-EMPTY.  Without it the
-- tie would be true at this record because nothing would meet it.
-- =====================================================================

module Wire (lam : V ℓ) (ordλ : IsOrd lam)
            (succλ : (d : V ℓ) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩)
            (∅∈λ : ⟨ ∅ ∈ lam ⟩)
            (gam : V ℓ) (ordγ : IsOrd gam) (γ∈λ : ⟨ gam ∈ lam ⟩)
            (#1∈γ : ⟨ (# 1) ∈ gam ⟩) where

  module KV = KValue lam ordλ succλ ∅∈λ gam ordγ γ∈λ

  open KFacts KV.facts using ( numK0; numK1; pairK; carrierK; arityK )

  module R = Refute KV.iA KV.iK KV.Kenv numK0 numK1 pairK carrierK arityK

  -- THE CARRIER IS INHABITED.  `# 0` is an ordinal, so it is in the next
  -- stage, and the carrier stage is above that.
  zero∈carrier : ⟨ fst (numeralL 0) ∈ fst (lookup KV.iA KV.Kenv) ⟩
  zero∈carrier = subst (λ u → ⟨ u ∈ Lset gam ⟩) (sym (numeralL-fst 0))
    (Lset-mono {α = gam} {β = # 1} #1∈γ
      {x = # 0} (ord∈Lset-suc (# 0) (numeral-ord 0)))

  module P = R.Point (numeralL 0) zero∈carrier

  -- THE DELIVERED TIE IS FALSE AT THE DELIVERED RECORD.
  tie-false : P.WCodesK → Empty.⊥
  tie-false = P.wCodesK-false

  -- And its other three conclusions hold there, as closed terms.
  live-other : ⟨ fst P.arS ∈ Lset lam ⟩
             × ⟨ fst (numeralL 0) ∈ Lset lam ⟩
             × ⟨ fst (numeralL 0) ∈ Lset lam ⟩
  live-other = P.other-conjuncts

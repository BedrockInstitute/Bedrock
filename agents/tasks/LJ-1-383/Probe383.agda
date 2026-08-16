{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.383] THE RESIDUE, TAKEN ONE PARAMETER AT A TIME.
--
-- THE LIVE RECORD already refutes four of the six by term:
-- `envK` and `defPairK` at `LJ-1-341/ProbeTies341.agda:185-190` and
-- `:231-238`, `witK` at `LJ-1-348/Refute348.agda:247-252`, `graphWitK`
-- at `LJ-1-351/Refute351.agda:408-412`, and the BINARY arity conjunct
-- at `LJ-1-347/Residue347.agda`.  THIS FILE closes the one gap the
-- record leaves: the UNARY arity residue, residue 2 of
-- `[LJ-1.338]`'s Supply telescope, stated VERBATIM at
-- `LJ-1-338/ProbeLeaf338.agda:124-128`, was never refuted by a term.
-- `LJ-1-347` swept its SITES and refuted only the binary shape.
--
-- THREE REFUTATIONS, ONE COUNTERMODEL:
--   residue 2 (`wUnArNum`), VERBATIM from ProbeLeaf338.agda:124-128;
--   residue 1 (`wArNum`), VERBATIM from ProbeLeaf338.agda:119-123;
--   the FULL unary tie `wUnCodesK`, verbatim from the chapter's
--   current text, src/L/Condensation.lagda.md:7246-7252.
--
-- THE COUNTERMODEL is `[LJ-1.347]`'s, rotated to the unary pair shape:
-- the arity slot is the singleton of the numeral one, `sgl1-not-numeral`
-- (`LJ-1-347/Elim347.agda`) refutes it as a numeral at EVERY index, and
-- the code is `pr (fst arS) (pr (# 0) (fst u))`, exactly the unary
-- shape, at `k := 0` and `a := u`.  The ambient facts come from the
-- chapter's own delivered code, `ChainZ` at :2820-2846 and `KTies` at
-- :6197-6259, exactly as `Residue347.agda` takes them.  The `sglS` and
-- `sglK` block below is `Residue347.agda:80-102` COPIED, attributed,
-- because it is private there.
--
-- NON-VACUITY, and it discriminates (C-42): the conjunct HOLDS at a
-- genuine numeral arity (`numeral-arity-holds`) and FAILS at the
-- singleton arity, ONE ARGUMENT APART in this one file, which is
-- `[LJ-1.350]`'s standard.  The tie's OTHER conclusions hold at the
-- witnesses (`un-other-conjuncts`), and every premise is a closed term.
-- Layer three, the delivered record, is `module Wire` below.
--
-- NO PATTERN MATCH SPLITS A NUMERAL INDEX (C-58): the only numeral
-- split in sight is `sgl1-not-numeral`, which `[LJ-1.347]` already
-- built through the library eliminator, imported here.
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
open PT using ( ∥_∥₁; ∣_∣₁ )

module LJ-1-383.Probe383 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

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
-- PART 1.  THE REFUTATIONS, GENERIC IN THE FRAME.
--
-- The five closure parameters are `KFacts` fields and nothing else,
-- exactly as `Residue347.agda` takes them.  `u` and `hu` say the
-- carrier slot has a MEMBER; without them the refutation would be
-- empty (C-45).
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

  -- The chapter's own ambient pair facts, at :2820-2846.
  module Z = ChainZ {n} K γ arityK

  -- The chapter's own singleton closure, at :6197-6259.
  open KTies A K γ numK0 pairK carrierK arityK using ( sgltK )

  private
    bnd : V ℓ
    bnd = fst (lookup K γ)

  -- COPIED from Residue347.agda:86-102, attributed there to
  -- `ChainZ.pair∈pr`, `prʟ-fst` and `isL-trans`: the singleton as a
  -- carrier element, and its closure into the bound.
  sglS : S → S
  sglS a = ⁅ fst a , fst a ⁆
         , isL-trans {x = fst (prʟ a a)} {y = ⁅ fst a , fst a ⁆}
             (subst (λ v → ⟨ ⁅ fst a , fst a ⁆ ∈ v ⟩) (sym (prʟ-fst a a))
               (Z.pair∈pr (fst a) (fst a)))
             (snd (prʟ a a))

  sglK : (a : S) → ⟨ fst a ∈ bnd ⟩ → ⟨ fst (sglS a) ∈ bnd ⟩
  sglK a ha = sgltK a (sglS a) refl ha

  module Point (u : S) (hu : ⟨ fst u ∈ fst (lookup A γ) ⟩) where

    -- THE ARITY SLOT.  Its set is the singleton of the numeral one.
    arS : S
    arS = sglS (numeralL 1)

    ar-fst : fst arS ≡ ⁅ # 1 , # 1 ⁆
    ar-fst = cong (λ w → ⁅ w , w ⁆) (numeralL-fst 1)

    arS∈K : ⟨ fst arS ∈ bnd ⟩
    arS∈K = sglK (numeralL 1) numK1

    uK : ⟨ fst u ∈ bnd ⟩
    uK = carrierK u hu

    -- THE UNARY CODE, of exactly the tie's pair shape, at `k := 0`
    -- and `a := u`.
    cU : S
    cU = prʟ arS (prʟ (numeralL 0) u)

    cU∈K : ⟨ fst cU ∈ bnd ⟩
    cU∈K = pairK arS (prʟ (numeralL 0) u) arS∈K
             (pairK (numeralL 0) u numK0 uK)

    wU : S
    wU = sglS cU

    wU∈K : ⟨ fst wU ∈ bnd ⟩
    wU∈K = sglK cU cU∈K

    cU∈wU : ⟨ fst cU ∈ fst wU ⟩
    cU∈wU = Z.b∈pair (fst cU) (fst cU)

    codeEqU : fst cU ≡ pr (fst arS) (pr (# 0) (fst u))
    codeEqU = prʟ-fst arS (prʟ (numeralL 0) u)
      ∙ cong (pr (fst arS))
          (prʟ-fst (numeralL 0) u ∙ cong₂ pr (numeralL-fst 0) refl)

    -- THE BINARY CODE, for residue 1.  The same arity slot, the same
    -- container, the binary pair shape.
    cB : S
    cB = prʟ arS (prʟ (numeralL 0) (prʟ u u))

    wB : S
    wB = sglS cB

    cB∈wB : ⟨ fst cB ∈ fst wB ⟩
    cB∈wB = Z.b∈pair (fst cB) (fst cB)

    codeEqB : fst cB ≡ pr (fst arS) (pr (# 0) (pr (fst u) (fst u)))
    codeEqB = prʟ-fst arS (prʟ (numeralL 0) (prʟ u u))
      ∙ cong (pr (fst arS))
          (prʟ-fst (numeralL 0) (prʟ u u)
            ∙ cong₂ pr (numeralL-fst 0) (prʟ-fst u u))

    -- RESIDUE 2, type VERBATIM from ProbeLeaf338.agda:124-128.
    WUnArNum : Type (ℓ-suc ℓ)
    WUnArNum = (w' : S) → (k : ℕ) → (c ar a : S) → ⟨ fst c ∈ fst w' ⟩
             → fst c ≡ pr (fst ar) (pr (# k) (fst a))
             → ∥ Σ[ m ∈ ℕ ] (fst ar ≡ # m) ∥₁

    wUnArNum-false : WUnArNum → Empty.⊥
    wUnArNum-false h = PT.rec Empty.isProp⊥
      (λ { (m , q) → sgl1-not-numeral m (sym ar-fst ∙ q) })
      (h wU 0 cU arS u cU∈wU codeEqU)

    -- RESIDUE 1, type VERBATIM from ProbeLeaf338.agda:119-123.
    WArNum : Type (ℓ-suc ℓ)
    WArNum = (w' : S) → (k : ℕ) → (c ar a b : S) → ⟨ fst c ∈ fst w' ⟩
           → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
           → ∥ Σ[ m ∈ ℕ ] (fst ar ≡ # m) ∥₁

    wArNum-false : WArNum → Empty.⊥
    wArNum-false h = PT.rec Empty.isProp⊥
      (λ { (m , q) → sgl1-not-numeral m (sym ar-fst ∙ q) })
      (h wB 0 cB arS u u cB∈wB codeEqB)

    -- THE FULL UNARY TIE, at the generic-frame form of the chapter's
    -- own type, src/L/Condensation.lagda.md:7246-7252.
    WUnCodesK : Type (ℓ-suc ℓ)
    WUnCodesK = (w' : S) → ⟨ fst w' ∈ bnd ⟩
              → (k : ℕ) → (c ar a : S) → ⟨ fst c ∈ fst w' ⟩
              → fst c ≡ pr (fst ar) (pr (# k) (fst a))
              → ⟨ fst ar ∈ bnd ⟩ × ⟨ fst a ∈ bnd ⟩
              × ∥ Σ[ m ∈ ℕ ] (fst ar ≡ # m) ∥₁

    unCodesK-false : WUnCodesK → Empty.⊥
    unCodesK-false h = PT.rec Empty.isProp⊥
      (λ { (m , q) → sgl1-not-numeral m (sym ar-fst ∙ q) })
      (h wU wU∈K 0 cU arS u cU∈wU codeEqU .snd .snd)

    -- NON-VACUITY, LAYER ONE.  The tie's OTHER conclusions hold at
    -- these witnesses, so the tie dies at a point where only the arity
    -- conjunct is refuted.
    un-other-conjuncts : ⟨ fst arS ∈ bnd ⟩ × ⟨ fst u ∈ bnd ⟩
    un-other-conjuncts = arS∈K , uK

    -- NON-VACUITY, LAYER TWO.  Every premise is a closed term above:
    -- `wU∈K`, `cU∈wU`, `codeEqU` are built, never assumed.

    -- NON-VACUITY, AND IT DISCRIMINATES ([LJ-1.350]'s standard).  The
    -- conjunct HOLDS at a genuine numeral arity, one argument away from
    -- the arity that kills it.
    numeral-arity-holds : ∥ Σ[ m ∈ ℕ ] (fst (numeralL 1) ≡ # m) ∥₁
    numeral-arity-holds = ∣ 1 , numeralL-fst 1 ∣₁

    -- And it FAILS at the singleton arity: `wUnArNum-false` above, at
    -- `arS := sglS (numeralL 1)`.  One argument apart, one file.

-- =====================================================================
-- PART 2.  NON-VACUITY, LAYER THREE.  AT THE DELIVERED RECORD.
--
-- `module KValue` (src/L/Condensation.lagda.md:7380) builds the ONE
-- `KFacts` value the chapter has.  The refutation runs on THAT record,
-- so this is not a parameters-green.  The one added hypothesis,
-- `#1-in-gam`, makes the carrier NON-EMPTY; without it the conjunct
-- would be true at this record because nothing would meet it (C-45).
-- Both blocks mirror Residue347.agda:226-262.
-- =====================================================================

module Wire (lam : V ℓ) (ordλ : IsOrd lam)
            (succλ : (d : V ℓ) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩)
            (∅∈λ : ⟨ ∅ ∈ lam ⟩)
            (gam : V ℓ) (ordγ : IsOrd gam) (γ∈λ : ⟨ gam ∈ lam ⟩)
            (#1∈γ : ⟨ (# 1) ∈ gam ⟩) where

  module KV = KValue lam ordλ succλ ∅∈λ gam ordγ γ∈λ

  open KFacts KV.facts using ( numK0; numK1; pairK; carrierK; arityK )

  module R = Refute KV.iA KV.iK KV.Kenv numK0 numK1 pairK carrierK arityK

  zero∈carrier : ⟨ fst (numeralL 0) ∈ fst (lookup KV.iA KV.Kenv) ⟩
  zero∈carrier = subst (λ u → ⟨ u ∈ Lset gam ⟩) (sym (numeralL-fst 0))
    (Lset-mono {α = gam} {β = # 1} #1∈γ
      {x = # 0} (ord∈Lset-suc (# 0) (numeral-ord 0)))

  module P = R.Point (numeralL 0) zero∈carrier

  -- ALL THREE REFUTATIONS RUN ON THE DELIVERED RECORD.
  residue2-false-at-record : P.WUnArNum → Empty.⊥
  residue2-false-at-record = P.wUnArNum-false

  residue1-false-at-record : P.WArNum → Empty.⊥
  residue1-false-at-record = P.wArNum-false

  unCodesK-false-at-record : P.WUnCodesK → Empty.⊥
  unCodesK-false-at-record = P.unCodesK-false

  -- And the tie's other conclusions hold there, as closed terms.
  live-other : ⟨ fst P.arS ∈ Lset lam ⟩ × ⟨ fst (numeralL 0) ∈ Lset lam ⟩
  live-other = P.un-other-conjuncts

  -- And the conjunct is satisfiable at a genuine numeral arity there.
  live-numeral-arity : ∥ Σ[ m ∈ ℕ ] (fst (numeralL 1) ≡ # m) ∥₁
  live-numeral-arity = P.numeral-arity-holds

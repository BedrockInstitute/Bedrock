{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.502] Does the consumer's formula survive t0 := N0 ?
--
-- `Kenv` has fourteen slots (Condensation.lagda.md:7389) and none is
-- spare, so a frame that needs `t0` to hold `numeralL 0` must point
-- `t0` at the same slot as `N0`.  [LJ-1.495] already put `N0 := i0`
-- there (agents/tasks/LJ-1-495/Probe495.agda:169).  The identification
-- is forced by the list.
--
-- `t0` and `t1` are NOT only fact indices.  They are variable indices
-- inside `SatGraphB.twelveB` (Condensation.lagda.md:2239-2260), in
-- four of the twelve rows.  This file asks whether the CONSUMER
-- survives one index serving two syntactic roles.
--
-- Nothing lands in src/.  No `TFacts` value is built here: `LFacts`
-- and `TFacts` are taken as HYPOTHESES, so the `envK-*` family and the
-- code readers that [LJ-1.499] and [LJ-1.500] hold are untouched.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-502.Probe502 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; IsOrd )
open import L.Axioms.Numerals {ℓ} using ( numeralL )
open import L.Coding.Model {ℓ} using ( prʟ; memClauseAt )
open import L.Condensation {ℓ} lem using
  ( module Mem; module MemAgree; module SatGraphB; module KValue )
open import L.Condensation.LowerAgree {ℓ} lem using ( LFacts )
open import L.Condensation.TwelveAgree {ℓ} lem using
  ( module AbstractFrame; TFacts )
open import L.Coding.Graph {ℓ} lem using ( twelveAt )
open import FOL.LevyHierarchy using ( Δ₀ )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; ∅ )
open InfinitySet {ℓ} using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- =====================================================================
-- W3.  THE `memBndAt` ROW ALONE, AT t0 := N0.
--
-- The other eleven rows are OMITTED as obligations: the consumer's
-- own twelve-row formula supplies them as an opaque argument, and
-- only the Mem row is rebuilt from the row lemma.
--
-- The splice is the collision detector.  `MemAgree.out` concludes at
-- `MemAgree.φB` (Condensation.lagda.md:4461), and the term below puts
-- that conclusion into the FIRST CONJUNCT position of the consumer's
-- `SatGraphB.twelveB` (:2241-2243) elaborated at t0 := N0, t1 := N1.
-- If the identification made the row lemma's conclusion a different
-- formula from the conjunct the consumer carries, `M.out hc , h .snd`
-- does not typecheck and the answer is NO here.
--
-- `LFacts` is a HYPOTHESIS.  The indices are instantiated at
-- t0 := N0 and t1 := N1 in the record type itself, so `tagEq0` and
-- `t0eq` become the SAME field type and `tagEq1` and `t1eq` likewise.
-- A frame that demanded two different numerals at one slot would show
-- as an unsatisfiable telescope right here.
-- =====================================================================

module W3 {n : ℕ}
  (N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 K : Fin (5 + n))
  (γ : S ^ (11 + n))
  (lf : LFacts {n} N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 N0 N1 K γ)
  where

  open LFacts lf

  arityK : (N v : S) → ⟨ fst v ∈ fst N ⟩
         → ⟨ fst N ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
         → ⟨ fst v ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
  arityK N v hv hNK = transK v N hv hNK

  -- The Mem row lemma, at the IDENTIFIED indices.  The call is
  -- LowerAgree.lagda.md:255-260 with `t0` replaced by `N0` and `t1` by
  -- `N1`, and nothing else changed.
  module M = MemAgree {11 + n} (suc (suc zero)) (suc zero) zero
               (suc (suc (suc (suc (suc (suc N0))))))
               (suc (suc (suc (suc (suc (suc K))))))
               (suc (suc (suc (suc (suc (suc N0))))))
               (suc (suc (suc (suc (suc (suc N1)))))) γ
               tagEq0 numK0
               (λ a b aK bK → innerK 0 (prʟ a b) (pairK a b aK bK))
               (λ a b aK bK → pairK a b aK bK) arityK (codesK 0) (valK 0)
               t0eq t1eq t0K num1K envK-mem envInK-mem
               valV valW

  memBndAt-at-identified :
      (w : Fin (5 + n))
    → ⟨ γ ⊨ memClauseAt (suc (suc zero)) (suc zero) zero ⟩
    → ⟨ γ ⊨ SatGraphB.twelveB {n} w K N0 N1 N2 N3 N4 N5
                               N6 N7 N8 N9 N10 N11 N0 N1 ⟩
    → ⟨ γ ⊨ SatGraphB.twelveB {n} w K N0 N1 N2 N3 N4 N5
                               N6 N7 N8 N9 N10 N11 N0 N1 ⟩
  memBndAt-at-identified w hc h = M.out hc , h .snd

memBndAt-at-identified = W3.memBndAt-at-identified


-- =====================================================================
-- THE CHEAPEST WITNESS, and the brief says check it first: the Δ₀
-- certificate of the consumer's formula, at the identification.
--
-- `twelveB` and `Δ₀-twelveB` (Condensation.lagda.md:2239, :2262) are
-- TOTAL functions of their sixteen `Fin (5 + n)` arguments, so this
-- term cannot fail on elaboration alone.  It is written down because
-- the brief asks for the shape to be checked unhurt, and it records
-- that the identification changes no Δ₀ derivation.
-- =====================================================================

Δ₀-twelveB-at-identified :
    {n : ℕ} (w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 : Fin (5 + n))
  → Δ₀ (SatGraphB.twelveB {n} w K N0 N1 N2 N3 N4 N5
                           N6 N7 N8 N9 N10 N11 N0 N1)
Δ₀-twelveB-at-identified {n} w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 =
  SatGraphB.Δ₀-twelveB {n} w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 N0 N1

-- =====================================================================
-- THE OBLIGATION.  All twelve rows, at t0 := N0 and t1 := N1, with the
-- downstream row lemmas STILL APPLYING.
--
-- `AbstractFrame` (TwelveAgree.lagda.md:337) is the tree's own
-- composer: it drives `LowerAgree` (LowerAgree.lagda.md:226) and
-- `UpperAgree`, which apply `MemAgree`, `EqAgree`, `AllInAgree` and
-- `ExInAgree` -- the four rows that name `t0` and `t1` -- and it
-- concludes at `SatGraphB.twelveB` (TwelveAgree.lagda.md:527-537).
-- Instantiating it at t0 := N0, t1 := N1 puts the identification
-- through every downstream row lemma at once.
--
-- `TFacts` is a HYPOTHESIS.  No `TFacts` value is built here, so the
-- `envK-*` family and the code readers stay untouched: [LJ-1.499] and
-- [LJ-1.500] hold those and are running.
-- =====================================================================

module Twelve {n : ℕ}
  (N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 K : Fin (5 + n))
  (γ' : S ^ (11 + n))
  (sucK : (a : S) → ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
          → ⟨ sucV (fst a) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (tf : TFacts {n} N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 N0 N1 K γ')
  where

  module AF = AbstractFrame {n} N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11
                N0 N1 K γ' sucK tf

  -- THE OBLIGATION.  The twelve rows of `SatGraphB.twelveB`,
  -- elaborated at t0 := N0 and t1 := N1, discharged by the downstream
  -- row lemmas.
  twelveB-at-identified :
      (w : Fin (5 + n))
    → ⟨ γ' ⊨ twelveAt (suc (suc zero)) (suc zero) zero ⟩
    → ⟨ γ' ⊨ SatGraphB.twelveB {n} w K N0 N1 N2 N3 N4 N5
                               N6 N7 N8 N9 N10 N11 N0 N1 ⟩
  twelveB-at-identified = AF.twelve-out

  -- The other direction, because the consumer needs both and a
  -- one-way survival would not settle the question.
  twelveB-at-identified-back :
      (w : Fin (5 + n))
    → ⟨ γ' ⊨ SatGraphB.twelveB {n} w K N0 N1 N2 N3 N4 N5
                               N6 N7 N8 N9 N10 N11 N0 N1 ⟩
    → ⟨ γ' ⊨ twelveAt (suc (suc zero)) (suc zero) zero ⟩
  twelveB-at-identified-back = AF.twelve-back

twelveB-at-identified = Twelve.twelveB-at-identified
twelveB-at-identified-back = Twelve.twelveB-at-identified-back


-- =====================================================================
-- WHAT THE IDENTIFICATION COSTS, AT KValue'S OWN FRAME.
--
-- The identification makes ONE slot carry two field positions.  The
-- record is then only inhabitable if the two positions want the SAME
-- value at that slot.  They do, and this is the arithmetic:
--
--   t0 := N0 = i0.  `tagEq0` (TwelveAgree.lagda.md:132) wants
--   `numeralL 0` at slot N0; `t0eq` (:186) wants `numeralL 0` at slot
--   t0.  One slot, one numeral, one proof.
--
--   t1 := N1 = i1.  `tagEq1` (:133) wants `numeralL 1` at slot N1;
--   `t1eq` (:187) wants `numeralL 1` at slot t1.  The same.
--
-- The tags line up because `t0` is the tag-0 index and `t1` is the
-- tag-1 index, and `Kenv` (Condensation.lagda.md:7389-7393) puts
-- `numeralL 0` at `i0` and `numeralL 1` at `i1`.  That is why the
-- identification is free and not merely legal.
--
-- These are the two `refl`s that [LJ-1.501] measured
-- (agents/tasks/LJ-1-501/Probe501.agda:57-63), restated AT THE
-- IDENTIFIED INDICES so that one term stands in both positions.
-- =====================================================================

module AtKValue
  (lam : V ℓ) (ordλ : IsOrd lam)
  (succλ : (d : V ℓ) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ lam ⟩)
  (gam : V ℓ) (ordγ : IsOrd gam) (γ∈λ : ⟨ gam ∈ lam ⟩) where

  open KValue lam ordλ succλ ∅∈λ gam ordγ γ∈λ

  -- One proof, two field positions: `tagEq0` and `t0eq`.
  slot0-serves-both : (c1 c2 c3 c4 c5 c6 : S)
                    → fst (lookup (suc (suc (suc (suc (suc (suc i0))))))
                             (c6 ∷ c5 ∷ c4 ∷ c3 ∷ c2 ∷ c1 ∷ Kenv))
                      ≡ fst (numeralL 0)
  slot0-serves-both c1 c2 c3 c4 c5 c6 = refl

  -- One proof, two field positions: `tagEq1` and `t1eq`.
  slot1-serves-both : (c1 c2 c3 c4 c5 c6 : S)
                    → fst (lookup (suc (suc (suc (suc (suc (suc i1))))))
                             (c6 ∷ c5 ∷ c4 ∷ c3 ∷ c2 ∷ c1 ∷ Kenv))
                      ≡ fst (numeralL 1)
  slot1-serves-both c1 c2 c3 c4 c5 c6 = refl

slot0-serves-both = AtKValue.slot0-serves-both
slot1-serves-both = AtKValue.slot1-serves-both

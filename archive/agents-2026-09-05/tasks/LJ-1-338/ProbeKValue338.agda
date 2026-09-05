{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.338] PROBE 1.  DOES `module KValue` TRANSPORT TO THE AMBIENT
-- CARRIER?
--
-- `[LJ-1.336]` found `module KValue` at
-- src/L/Condensation.lagda.md:7264-7318 and did not use it.  It builds
-- the one `KFacts` VALUE at the L class, from the same four hypotheses
-- the ambient tie probe needed and from the same `L.Coding.Bound`.  The
-- brief asks whether that block transports to the ambient carrier, or
-- whether ambient needs its own.
--
-- THE METHOD IS WAVE 1's AND WAVE 2's: copy the block VERBATIM and count
-- the changed lines.  Below the marker, every line of `module KValue` is
-- the chapter's line, character for character.  Above the marker sit the
-- ambient names the block reaches, and the count of THOSE lines is the
-- transport price.
--
-- ONE agda process under GHCRTS="-A64m -I0 -M8g".

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

open import FOL.ZFStructure using ( module hPropStructure; _↾_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆; ∅ ) renaming ( module InfinitySet to Inf )
open Inf using ( #_; sucV )
open import Cubical.Data.Unit using ( tt* )

import LJ-1-336.GenDirty

module LJ-1-338.ProbeKValue338 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( Lset; IsOrd; Lset-mono )
open import L.Coding.Bound {ℓ} lem renaming ( module Bound to BoundL )

import LJ-1-297.ProbeLJ1297A {ℓ} lem as P1297A

-- The ambient class supplies all eight parameters, in `[LJ-1.302]`'s and
-- `[LJ-1.336]`'s shape.
module GD = LJ-1-336.GenDirty {ℓ} P1297A.Full
  (λ {x} {y} → P1297A.Full-tr {x} {y})
  (λ k → # k , tt*) (λ k → refl)
  (λ a b → ⁅ fst a , fst b ⁆ , tt*) (λ a b → refl)
  (λ a → sucV (fst a) , tt*) (λ a → refl)

open hPropStructure (𝒮ᵥ ↾ P1297A.Full) using ( S )
open GD.W1.KFactsNS using ( KFacts )
open GD.W1.KFactsNS.KFacts
open GD.W1 using ( KFactsCons )
open GD.W1.GM using ( prʟ; prʟ-fst )
open GD.W1.GM.AbsL using ( _^_ )

-- =====================================================================
-- THE AMBIENT ADAPTER.  Everything `module KValue` reaches that is
-- SPELLED at the L class and must be re-spelled at the ambient one.
-- Three names, and this block is the transport price.
-- =====================================================================

-- 1.  The numerals as ambient sorts.  `L.Axioms.Numerals.numeralL`
--     lands in L; here the class is trivial, so the witness is `tt*`.
numeralL : ℕ → S
numeralL k = # k , tt*

-- 2.  A stage as an ambient sort.  `L.Axioms.Basic.LsetS` proves
--     `isL (Lset β)`; here the class is trivial again.
LsetS : (β : V ℓ) → IsOrd β → S
LsetS β oβ = Lset β , tt*

-- 3.  The bound, with its two L presentations re-spelled.  `Bound` is
--     NOT re-proved: `BoundOver` is already generic in the tower and
--     `Bound`'s own `num∈λ` and `prʟ∈λ` are its facts pushed through the
--     L SORT.  Push them through the ambient sort instead.
module Bound (lam : V ℓ) (ordλ : IsOrd lam)
             (succλ : (d : V ℓ) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩)
             (∅∈λ : ⟨ ∅ ∈ lam ⟩) where

  module B0 = BoundL lam ordλ succλ ∅∈λ
  open B0 public using ( trans∈λ )

  num∈λ : (k : ℕ) → ⟨ fst (numeralL k) ∈ Lset lam ⟩
  num∈λ k = B0.#∈Tλ k

  prʟ∈λ : (a b : S) → ⟨ fst a ∈ Lset lam ⟩ → ⟨ fst b ∈ Lset lam ⟩
        → ⟨ fst (prʟ a b) ∈ Lset lam ⟩
  prʟ∈λ a b ha hb = subst (λ w → ⟨ w ∈ Lset lam ⟩) (sym (prʟ-fst a b))
    (B0.pr∈λ (fst a) (fst b) ha hb)

-- =====================================================================
-- MARKER.  Everything below is COPIED VERBATIM from
-- src/L/Condensation.lagda.md:7264-7318.  Nothing is changed.
-- =====================================================================

module KValue (lam : V ℓ) (ordλ : IsOrd lam)
              (succλ : (d : V ℓ) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩)
              (∅∈λ : ⟨ ∅ ∈ lam ⟩)
              (gam : V ℓ) (ordγ : IsOrd gam) (γ∈λ : ⟨ gam ∈ lam ⟩) where

  module B = Bound lam ordλ succλ ∅∈λ

  -- Fourteen slots: the carrier, the bound, and the twelve arity tags.
  -- The carrier is a stage BELOW the bound, which is the real shape.
  Kenv : S ^ 14
  Kenv = LsetS gam ordγ ∷ LsetS lam ordλ
       ∷ numeralL 0 ∷ numeralL 1 ∷ numeralL 2 ∷ numeralL 3
       ∷ numeralL 4 ∷ numeralL 5 ∷ numeralL 6 ∷ numeralL 7
       ∷ numeralL 8 ∷ numeralL 9 ∷ numeralL 10 ∷ numeralL 11 ∷ []

  iA iK i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 : Fin 14
  iA = zero
  iK = suc zero
  i0 = suc (suc zero)
  i1 = suc (suc (suc zero))
  i2 = suc (suc (suc (suc zero)))
  i3 = suc (suc (suc (suc (suc zero))))
  i4 = suc (suc (suc (suc (suc (suc zero)))))
  i5 = suc (suc (suc (suc (suc (suc (suc zero))))))
  i6 = suc (suc (suc (suc (suc (suc (suc (suc zero)))))))
  i7 = suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
  i8 = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
  i9 = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))
  i10 = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))
  i11 = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))

  facts : KFacts iA iK i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 Kenv
  facts = record
    { tagEq0 = refl ; tagEq1 = refl ; tagEq2 = refl ; tagEq3 = refl
    ; tagEq4 = refl ; tagEq5 = refl ; tagEq6 = refl ; tagEq7 = refl
    ; tagEq8 = refl ; tagEq9 = refl ; tagEq10 = refl ; tagEq11 = refl
    ; numK0 = B.num∈λ 0 ; numK1 = B.num∈λ 1 ; numK2 = B.num∈λ 2
    ; numK3 = B.num∈λ 3 ; numK4 = B.num∈λ 4 ; numK5 = B.num∈λ 5
    ; numK6 = B.num∈λ 6 ; numK7 = B.num∈λ 7 ; numK8 = B.num∈λ 8
    ; numK9 = B.num∈λ 9 ; numK10 = B.num∈λ 10 ; numK11 = B.num∈λ 11
    ; innerK = λ k a ha → B.prʟ∈λ (numeralL k) a (B.num∈λ k) ha
    ; innerPairK = λ k a b ha hb →
        B.prʟ∈λ (numeralL k) (prʟ a b) (B.num∈λ k) (B.prʟ∈λ a b ha hb)
    ; pairK = λ a b ha hb → B.prʟ∈λ a b ha hb
    ; carrierK = λ v hv → Lset-mono {α = lam} {β = gam} γ∈λ {x = fst v} hv
    ; arityK = λ N v v∈N N∈K → B.trans∈λ {x = fst N} {y = fst v} v∈N N∈K }

  -- The value is a VALUE, and this is the test: `KFactsCons` is the
  -- tree's own consumer and it accepts the record at its own indices.
  consed : (c : S)
         → KFacts (suc iA) (suc iK) (suc i0) (suc i1) (suc i2) (suc i3)
             (suc i4) (suc i5) (suc i6) (suc i7) (suc i8) (suc i9)
             (suc i10) (suc i11) (c ∷ Kenv)
  consed c = KFactsCons iA iK i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11
               Kenv c facts

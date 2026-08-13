-- LJ-1.158, probe L2.  THE CONTROLLED PAIR AT `lower`.
--
-- `[LJ-1.155]` measured the telescope-to-record collapse on `UpperAgree`'s 36
-- hypotheses: `DeadCode.DeadCodeReachable` 2,652 ms to 25 ms.  It named its own
-- unmeasured term: `TwelveAgree` carries a longer telescope and 13,976 of the
-- 24,469 ms, and a measured cure does not transfer by analogy (P-l).
--
-- THIS FILE IS THE RECORD SIDE of that pair at `lower`.  It carries 37
-- hypotheses and the SAME eight definitions that do no work, so the two sides
-- differ in the statement of the block and in nothing else.
--
-- Every hypothesis is `src/L/Condensation/LowerAgree.lagda.md` verbatim,
-- machine-extracted by `agents/tasks/LJ-1-158/gen_probe.py`.
--
-- Read with `agda --profile=internal`.

{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-158.ProbeLJ1158L2 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; _∧̇_ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Axioms.Numerals {ℓ} using ( numeralL )
open import L.Coding.Model {ℓ}
  using ( prʟ; prʟ-fst; envSetAt; envOverAt; tmValAt; subValAt
        ; memClauseAt; eqClauseAt; andClauseAt; orClauseAt
        ; impClauseAt; negClauseAt )
open import L.Coding.Graph {ℓ} lem using ( twelveAt )
open import L.Condensation {ℓ} lem using
  ( envHypB2; module Mem; module Eq; module And; module Or; module Imp
  ; module Neg; module MemAgree; module EqAgree; module AndAgree
  ; module OrAgree; module ImpAgree; module NegAgree )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet using ( #_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )
open import L.Condensation.LowerAgree {ℓ} lem using ( someEnvDef )

record RFacts {n : ℕ}
  (N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K : Fin (5 + n))
  (γ : S ^ (11 + n)) : Type (ℓ-suc ℓ) where
  field
    tagEq0 : fst (lookup (suc (suc (suc (suc (suc (suc N0)))))) γ) ≡ fst (numeralL 0)
    tagEq1 : fst (lookup (suc (suc (suc (suc (suc (suc N1)))))) γ) ≡ fst (numeralL 1)
    tagEq2 : fst (lookup (suc (suc (suc (suc (suc (suc N2)))))) γ) ≡ fst (numeralL 2)
    tagEq3 : fst (lookup (suc (suc (suc (suc (suc (suc N3)))))) γ) ≡ fst (numeralL 3)
    tagEq4 : fst (lookup (suc (suc (suc (suc (suc (suc N4)))))) γ) ≡ fst (numeralL 4)
    tagEq5 : fst (lookup (suc (suc (suc (suc (suc (suc N5)))))) γ) ≡ fst (numeralL 5)
    numK0 : ⟨ fst (numeralL 0) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
    numK1 : ⟨ fst (numeralL 1) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
    numK2 : ⟨ fst (numeralL 2) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
    numK3 : ⟨ fst (numeralL 3) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
    numK4 : ⟨ fst (numeralL 4) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
    numK5 : ⟨ fst (numeralL 5) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
    innerK : (k : ℕ) (p : S) → ⟨ fst p ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
      → ⟨ fst (prʟ (numeralL k) p) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
    pairK : (a b : S) → ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
      → ⟨ fst b ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
      → ⟨ fst (prʟ a b) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
    codesK : (k : ℕ) (c ar a b : S) → ⟨ fst c ∈ fst (lookup (suc (suc zero)) γ) ⟩
      → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
      → ⟨ fst ar ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
      × ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
      × ⟨ fst b ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
    codesK-un : (k : ℕ) (c ar a : S) → ⟨ fst c ∈ fst (lookup (suc (suc zero)) γ) ⟩
      → fst c ≡ pr (fst ar) (pr (# k) (fst a))
      → ⟨ fst ar ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
      × ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
    valK : (k : ℕ) (c ar a b yc : S) → ⟨ fst c ∈ fst (lookup (suc (suc zero)) γ) ⟩
      → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
      → ⟨ pr (fst c) (fst yc) ∈ fst (lookup (suc zero) γ) ⟩
      → ⟨ fst yc ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
    valK-un : (k : ℕ) (c ar a yc : S) → ⟨ fst c ∈ fst (lookup (suc (suc zero)) γ) ⟩
      → fst c ≡ pr (fst ar) (pr (# k) (fst a))
      → ⟨ pr (fst c) (fst yc) ∈ fst (lookup (suc zero) γ) ⟩
      → ⟨ fst yc ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
    t0eq : fst (lookup (suc (suc (suc (suc (suc (suc t0)))))) γ) ≡ fst (numeralL 0)
    t1eq : fst (lookup (suc (suc (suc (suc (suc (suc t1)))))) γ) ≡ fst (numeralL 1)
    t0K : ⟨ fst (lookup (suc (suc (suc (suc (suc (suc t0)))))) γ)
      ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
    num1K : ⟨ fst (numeralL 1) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
    envK-mem : (yc b a ar c E : S) → ⟨ (E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
      envSetAt zero (suc (suc (suc (suc zero))))
      (suc (suc (suc (suc (suc (suc zero)))))) ⟩
      → ⟨ fst E ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
    envK-neg : (ya yc a ar c E : S) → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨
      envSetAt zero (suc (suc (suc (suc zero))))
      (suc (suc (suc (suc (suc (suc zero)))))) ⟩
      → ⟨ fst E ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
    envK-imp : (E yb ya yc b a ar c : S) → ⟨ (E ∷ yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
      envSetAt zero (suc (suc (suc (suc (suc (suc zero))))))
      (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) ⟩
      → ⟨ fst E ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
    envInK-mem : (yc b a ar c E z : S) → ⟨ (z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
      envOverAt zero (suc (suc (suc (suc (suc zero)))))
      (suc (suc (suc (suc (suc (suc (suc zero))))))) ⟩
      → ⟨ fst z ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
    envInK-neg : (ya yc a ar c E z : S) → ⟨ (z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨
      envOverAt zero (suc (suc (suc (suc (suc zero)))))
      (suc (suc (suc (suc (suc (suc (suc zero))))))) ⟩
      → ⟨ fst z ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
    envInK-imp : (E ya yc b a ar c z : S) → ⟨ (z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
      envOverAt zero (suc (suc (suc (suc (suc (suc zero))))))
      (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) ⟩
      → ⟨ fst z ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
    valV : (E yc b a ar c z v w : S) → ⟨ (w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
      tmValAt (suc (suc (suc (suc (suc (suc zero))))))
      (suc (suc zero))
      (suc zero) ⟩
      → ⟨ fst v ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc K)))))))))))))
      (z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)) ⟩
    valW : (E yc b a ar c z v w : S) → ⟨ (w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
      tmValAt (suc (suc (suc (suc (suc zero)))))
      (suc (suc zero))
      zero ⟩
      → ⟨ fst w ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc K))))))))))))))
      (v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)) ⟩
    transK : (x a : S) → ⟨ fst x ∈ fst a ⟩
      → ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
      → ⟨ fst x ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
    subK₁-and : (x y yc b a ar c : S) → ⟨ (x ∷ y ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
      subValAt {7 + (11 + n)} (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
      (suc (suc (suc (suc (suc zero)))))
      (suc (suc (suc (suc zero))))
      (suc zero) ⟩
      → ⟨ fst y ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
    subK₀-and : (y ya yc b a ar c : S) → ⟨ (y ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
      subValAt {7 + (11 + n)} (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
      (suc (suc (suc (suc (suc zero)))))
      (suc (suc (suc zero)))
      zero ⟩
      → ⟨ fst y ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
    subK₁-imp : (E yb ya yc b a ar c : S) → ⟨ (E ∷ yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
      subValAt (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
      (suc (suc (suc (suc (suc (suc zero))))))
      (suc (suc (suc (suc (suc zero)))))
      (suc (suc zero)) ⟩
      → ⟨ fst ya ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
    subK₀-imp : (E yb ya yc b a ar c : S) → ⟨ (E ∷ yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
      subValAt (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
      (suc (suc (suc (suc (suc (suc zero))))))
      (suc (suc (suc (suc zero))))
      (suc zero) ⟩
      → ⟨ fst yb ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
    someEnv : someEnvDef {n} K γ
    subK-neg : (ya yc a ar c E : S) → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨
      subValAt (suc (suc (suc (suc (suc (suc (suc zero)))))))
      (suc (suc (suc (suc zero))))
      (suc (suc (suc zero)))
      (suc zero) ⟩
      → ⟨ fst ya ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩

module Big {n : ℕ}
  (N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K : Fin (5 + n))
  (γ : S ^ (11 + n))
  (f : RFacts N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K γ)
  where

  -- Eight definitions that do no work.  Their stored types carry whatever the
  -- module telescope is, and `DeadCode.DeadCodeReachable` walks those types.

  d0 : (a : S) → ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
     → ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
  d0 a h = h

  d1 : (a : S) → ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
     → ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
  d1 a h = h

  d2 : (a : S) → ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
     → ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
  d2 a h = h

  d3 : (a : S) → ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
     → ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
  d3 a h = h

  d4 : (a : S) → ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
     → ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
  d4 a h = h

  d5 : (a : S) → ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
     → ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
  d5 a h = h

  d6 : (a : S) → ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
     → ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
  d6 a h = h

  d7 : (a : S) → ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
     → ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
  d7 a h = h

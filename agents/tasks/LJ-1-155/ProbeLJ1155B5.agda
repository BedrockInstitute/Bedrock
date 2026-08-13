-- LJ-1.155, probe B5.  BISECTING THE RECORD WALL.
--
-- Probe B4 stated `UpperAgree`'s 36 telescope hypotheses as a RECORD and
-- exhausted an 8 GB heap in 117 s.  Probe B1 stated the SAME 36 as a module
-- telescope and cost 5.7 s.  This file narrows the wall to a field range.
--
-- FIELDS 0 to 22 of 36, named: tagEq6, tagEq7, tagEq8, tagEq9, tagEq10, tagEq11, numK6, numK7, numK8, numK9, numK10, numK11, innerK, pairK, arityK, codesK, codesK-un, valK, valK-un, t0eq, t1eq, t0K, num1K
--
-- Every field is `src/L/Condensation/UpperAgree.lagda.md:80-178` verbatim,
-- machine-extracted by `agents/tasks/LJ-1-155/gen_record_probe.py`.
--
-- Read with `agda --profile=internal`.

{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-155.ProbeLJ1155B5 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _∈̇_; _∧̇_ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Axioms.Numerals {ℓ} using ( numeralL; sucʟ; sucʟ-fst )
open import L.Coding.Model {ℓ}
  using ( prʟ; prʟ-fst; envSetAt; envOverAt; tmValAt; consAtL; subValSuccAt )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet using ( #_; sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

record UFacts {n : ℕ}
  (N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K : Fin (5 + n))
  (γ : S ^ (11 + n)) : Type (ℓ-suc ℓ) where
  field
    tagEq6 : fst (lookup (suc (suc (suc (suc (suc (suc N6)))))) γ) ≡ fst (numeralL 6)
    tagEq7 : fst (lookup (suc (suc (suc (suc (suc (suc N7)))))) γ) ≡ fst (numeralL 7)
    tagEq8 : fst (lookup (suc (suc (suc (suc (suc (suc N8)))))) γ) ≡ fst (numeralL 8)
    tagEq9 : fst (lookup (suc (suc (suc (suc (suc (suc N9)))))) γ) ≡ fst (numeralL 9)
    tagEq10 : fst (lookup (suc (suc (suc (suc (suc (suc N10)))))) γ) ≡ fst (numeralL 10)
    tagEq11 : fst (lookup (suc (suc (suc (suc (suc (suc N11)))))) γ) ≡ fst (numeralL 11)
    numK6 : ⟨ fst (numeralL 6) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
    numK7 : ⟨ fst (numeralL 7) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
    numK8 : ⟨ fst (numeralL 8) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
    numK9 : ⟨ fst (numeralL 9) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
    numK10 : ⟨ fst (numeralL 10) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
    numK11 : ⟨ fst (numeralL 11) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
    innerK : (k : ℕ) (p : S) → ⟨ fst p ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
      → ⟨ fst (prʟ (numeralL k) p) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
    pairK : (a b : S) → ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
      → ⟨ fst b ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
      → ⟨ fst (prʟ a b) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
    arityK : (N v : S) → ⟨ fst v ∈ fst N ⟩
      → ⟨ fst N ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
      → ⟨ fst v ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
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

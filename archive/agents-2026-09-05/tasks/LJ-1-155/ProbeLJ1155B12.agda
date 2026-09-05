-- LJ-1.155, probe B8.  BISECTING THE RECORD WALL.
--
-- Probe B4 stated `UpperAgree`'s 36 telescope hypotheses as a RECORD and
-- exhausted an 8 GB heap in 117 s.  Probe B1 stated the SAME 36 as a module
-- telescope and cost 5.7 s.  This file narrows the wall to a field range.
--
-- FIELDS 30 to 30 of 36, named: sucK
--
-- Every field is `src/L/Condensation/UpperAgree.lagda.md:80-178` verbatim,
-- machine-extracted by `agents/tasks/LJ-1-155/gen_record_probe.py`.
--
-- Read with `agda --profile=internal`.

{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-155.ProbeLJ1155B12 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

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
    f : (a : S) → ⟨ sucV (fst a) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩

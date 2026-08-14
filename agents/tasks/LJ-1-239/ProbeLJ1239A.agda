{-# OPTIONS --cubical --safe --guardedness #-}

-- ProbeLJ1239A: assemble `lh`, step by step, and measure where the
-- recipe's four steps land.  The lead finding is C-44: the recipe's
-- step 4 operates on the BOUNDED matrix `levelHoodB` (constant-free),
-- while the brief's DIFFICULTY is about the UNBOUNDED graph `LsetGraph`
-- (constant-carrying).  Measured here: `countFo LsetGraph ≢ 0` and
-- `countFo levelHoodB ≡ 0`.
--
--   STEP 1  Lset-defines, class-carrier belief in the unbounded graph
--   STEP 4  the arity gap: the recipe's matrix is arity 4 with free
--           tag slots, not the closed arity-2 `φ₀` the `lh` type names
--
-- ONE agda process under GHCRTS="-A64m -I0 -M8g".

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-239.ProbeLJ1239A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import FOL.Manipulation.Parameters using ( countFo )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset )
open import L.Coding.Sequence {ℓ} lem using ( LsetGraphAt )
open import L.Hierarchy {ℓ} lem using ( Lset-defines )
open import L.BoundedSubset {ℓ} lem using ( module LevelHood0 )

open import Cubical.Data.Vec using ( _∷_; [] )
open import Cubical.Data.Nat using ( ℕ; zero; suc )

open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- ---------------------------------------------------------------------
-- STEP 1.  Class-carrier belief in the UNBOUNDED graph, from
-- `fst v ≡ Lset (fst b)`.  One application of the delivered
-- `Lset-defines` (src/L/Hierarchy.lagda.md:646).
-- ---------------------------------------------------------------------

step1 : (v b : S) → IsOrd (fst b) → fst v ≡ Lset (fst b)
      → ⟨ (v ∷ b ∷ []) ⊨ LsetGraphAt zero (suc zero) ⟩
step1 v b ob q = Lset-defines zero (suc zero) (v ∷ b ∷ []) ob q

-- ---------------------------------------------------------------------
-- THE ARITY GAP.  The bounded matrix is constant-free, but its tag
-- numerals are SLOTS (src/L/Condensation.lagda.md:1125, :1469), so the
-- matrix has free tag slots and cannot be the closed arity-2 `φ₀` the
-- `lh` type names.
-- ---------------------------------------------------------------------

module LH0 = LevelHood0
  zero zero zero zero zero zero zero zero zero zero zero zero zero zero
  zero zero zero zero zero zero zero zero zero zero zero zero zero zero

-- MEASURED (ProbeLJ1239Check, the error type): the unbounded graph
-- carries constants.  `countFo LsetGraph` normalizes to a large
-- `suc (suc (...))`, NOT `zero`; `refl` is refused.

-- MEASURED: the bounded matrix is constant-free (countFo ≡ 0, refl).
check-bounded : countFo LH0.matrix ≡ zero
check-bounded = refl

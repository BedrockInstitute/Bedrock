{-# OPTIONS --cubical --safe --guardedness #-}

-- LJ-1.165 probe A.  THE TRANSFER'S BLOCKER, RE-MEASURED AT THE
-- MASTER'S OWN FORMULA.
--
-- [LJ-1.161] MEASURED a WALL at `refl : countFo LH.levelHoodΣ₁ ≡ 0`:
-- 20 minutes, 9.03 GB resident, no heap exhaustion, SIGTERM.  It named
-- one cure and did not price it: split, or carry the `countFo ≡ 0`
-- proof as a hypothesis instead of recomputing it.
--
-- P-l binds: a measured cure does not transfer by analogy, and a cost
-- measured at one formula is not a cost at another.  So this probe
-- re-measures in ASCENDING order of size and stops at the first term
-- that meets the criterion.
--
-- CRITERION, FIXED BEFORE THE RUN (D-1), and it is the report's:
--   20 minutes of wall time per agda invocation, GHCRTS="-A64m -I0 -M8g",
--   ONE process, cap NEVER raised.
--
-- BLOCK 1  the generic wrapper.  `extAtB` carries its argument TWICE,
--          at a VARIABLE subformula.  This is the structural reason the
--          level-hood formula holds the twelve-row table many times
--          over, and it is measured here, not inferred.
-- BLOCK 2  ONE copy of the twelve-row table:
--          `countFo (DefBodyB ..) ≡ 0`.  The wrappers reduce to it, so
--          the whole split cure stands or falls here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-165.ProbeLJ1165A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import FOL.Manipulation.Parameters using ( countFo )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.Condensation {ℓ} lem using ( DefBodyB; extAtB )
open import Cubical.Data.Nat using ( _+_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

-- =====================================================================
-- BLOCK 1.  THE GENERIC WRAPPER, at a VARIABLE subformula.
-- =====================================================================

cnt-extAtB : ∀ {n} (y K : Fin n) (φ : Formula S (suc n))
           → countFo (extAtB y K φ) ≡ countFo φ + (countFo φ + 0)
cnt-extAtB y K φ = refl

-- =====================================================================
-- BLOCK 2.  ONE COPY OF THE TWELVE-ROW TABLE.
-- =====================================================================

cnt-DefBodyB : ∀ {n} (w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1
                 : Fin (5 + n))
             → countFo (DefBodyB {n} w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11
                                 t0 t1) ≡ 0
cnt-DefBodyB w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 = refl

{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.676] PROBE.  The chapter's LevelHood {n} kernel, satisfied
-- at GENERIC n, arity 4 + n, K free.  Lands nothing in src/.
-- Builds none of the three consumer views (651/662 maps already green).
--
--   THE OBLIGATION  kernel-sat.  The class-carrier Σ₁ transfer of
--                   levelHoodB, the green term [LJ-1.669] delivered at
--                   n = 0 (Probe669.agda:117-121), instantiated at the
--                   chapter's own generic n.  W2: σ₁-up is already
--                   generic (src/FOL/Absoluteness.lagda.md:182-184);
--                   this file does not rewrite it.
--
--   NOT INHABITED   sat-at-level (666 NO-GO), sound-at-arity4
--                   (669 NO-GO), hoodsound-at-levelhood0 (661 NO-GO).
--                   The KFacts wall at n = 0 is a proof constraint on
--                   ADEQUACY through LeafAgree, not on this transfer
--                   (lj-1.675-report.md:250-253).  Slot arithmetic
--                   for that route is recorded below, not ridden.
--
-- ONE Agda process per run, GHCRTS wide caliber, set on the pane by
-- the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-676.Probe676 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import FOL.LevyHierarchy using ( Δ₀; Σ₁; σ-Δ₀; Π₁; π-Δ₀ )
open import FOL.Manipulation.Parameters using ( countFo )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.BoundedSubset {ℓ} lem using ( module LevelHood )

open import Cubical.Data.Vec using ( map )
open import Cubical.Data.Nat using ( _+_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))

module CS = hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ )

-- =====================================================================
-- PART 1.  THE CHAPTER'S KERNEL AT GENERIC n.
--
--   module LevelHood {n} (src/L/BoundedSubset.lagda.md:74-111):
--   env u ∷ v ∷ γ ∷ K ∷ extras, arity 4 + n, K free at slot 3.
--   All Fin slots are parameters, the delivered convention at n = 0
--   being zeros (agents/tasks/LJ-1-661/Probe661.agda:98-100).
--
--   SEALED (P-l, dev/LESSONS.md:2367).  Left transparent, a
--   satisfaction type names the whole bounded graph inside the
--   elaborator and was measured to wall the wide caliber at
--   [LJ-1.662] (Probe662.agda:102-108).
-- =====================================================================

module Pin {n : ℕ}
  (N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 : Fin (5 + n))
  (M0 M1 M2 M3 M4 M5 M6 M7 M8 M9 M10 M11 s0 s1 : Fin (7 + n)) where

  module LH = LevelHood {n} N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1
                          M0 M1 M2 M3 M4 M5 M6 M7 M8 M9 M10 M11 s0 s1

  opaque
    matrix : Formula CS.S (4 + n)
    matrix = LH.levelHoodB

    Δ₀-matrix : Δ₀ matrix
    Δ₀-matrix = LH.Δ₀-levelHoodB

    -- The matrix is a normal form: its erasure count is `refl`
    -- (first measured at agents/tasks/LJ-1-651/Probe651.agda:73-74,
    -- re-measured at n = 0 by Probe669.agda:87-88).
    count-matrix : countFo matrix ≡ 0
    count-matrix = refl

    -- The Δ₀ matrix itself, graded Σ₁ by the leaf constructor.
    -- K stays in the environment.
    Σ₁-matrix : Σ₁ matrix
    Σ₁-matrix = σ-Δ₀ Δ₀-matrix

  -- W2: the mathematics is the delivered σ₁-up
  -- (src/FOL/Absoluteness.lagda.md:182-185), instantiated at the
  -- generic arity the chapter already writes.  The generic form is
  -- not rewritten.  A deadline does not force a fixed-n copy.
  --
  -- σ₁-up (σ-Δ₀ d) = subst ⟨_⟩ (abs₀ d δ) at
  -- src/FOL/Absoluteness.lagda.md:184.  That is the Σ₁ statement's
  -- own transfer, not a mapΔ₀ of the certificate onto a foreign
  -- domain.
  kernel-sat-at :
    (δ : AbsL.SM ^ (4 + n))
    → ⟨ δ AbsL.⊨ᵐ matrix ⟩
    → ⟨ map fst δ AbsL.⊨ᵛ matrix ⟩
  kernel-sat-at = AbsL.σ₁-up Σ₁-matrix

  -- The reverse direction EXISTS at this carrier and also avoids
  -- mapΔ₀, but it is Π₁-down, not Σ₁-up
  -- (src/FOL/Absoluteness.lagda.md:187-190).  Recorded so the next
  -- brief does not rediscover it.  Same recording at n = 0:
  -- Probe669.agda:134-138.
  reverse-at :
    (δ : AbsL.SM ^ (4 + n))
    → ⟨ map fst δ AbsL.⊨ᵛ matrix ⟩
    → ⟨ δ AbsL.⊨ᵐ matrix ⟩
  reverse-at = AbsL.π₁-down (π-Δ₀ Δ₀-matrix)

-- =====================================================================
-- THE OBLIGATION.  Lifted out of the parameterised module so the
-- witness meter can read the name (scripts/pod/witness.py:278;
-- measured on [LJ-1.651] Probe651.agda:152-156).
-- =====================================================================

kernel-sat = Pin.kernel-sat-at

-- =====================================================================
-- PART 2.  SLOT ARITHMETIC FOR THE ADEQUACY ROUTE, NOT RIDDEN.
--
--   [LJ-1.662] measured that twelve numeral columns cannot come from
--   five committed slots at n = 0 (lj-1.662-report.md:46-49).
--   [LJ-1.666] recorded that LevelHood {n} for n ≥ 14 has room
--   (review-of-sat-at-level.md:117-119) and that closing back to
--   arity 2 loses the columns.
--
--   This file does not inhabit LeafAgree and does not build a
--   graphBndAt ↔ LsetGraphAt bridge (no such theorem in src/:
--   agents/tasks/LJ-1-662/review-of-hoodexists.md:39-43).  The
--   counts below are the room the NEXT brief would use.
--
--   Outer env of levelHoodB, arity 4 + n
--   (src/L/BoundedSubset.lagda.md:68-72, :108):
--     slot 0  unused u     (can hold a numeral)
--     slot 1  v            (committed: the value)
--     slot 2  γ            (committed: the ordinal)
--     slot 3  K            (committed: the free bound)
--     slots 4 .. 3 + n     extras, n of them
--   Usable for numerals without clobbering v, γ, K: 1 + n.
--   Twelve numerals need 1 + n ≥ 12, i.e. n ≥ 11.
-- =====================================================================

usable-numeral-slots : ℕ → ℕ
usable-numeral-slots n = suc n

numerals-needed : ℕ
numerals-needed = 12

room-at-11 : usable-numeral-slots 11 ≡ 12
room-at-11 = refl

k-free-slot : ℕ
k-free-slot = 3

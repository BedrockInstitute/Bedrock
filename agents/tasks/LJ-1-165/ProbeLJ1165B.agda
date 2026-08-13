{-# OPTIONS --cubical --safe --guardedness #-}

-- LJ-1.165 probe B.  [LJ-1.161]'s BLOCK-3 WALL: BISECTED, DIAGNOSED,
-- HALF CURED.
--
-- [LJ-1.161] recorded 20 min 0 s and 9.03 GB, with NO heap exhaustion,
-- for its block 3: the transfer at the LEVEL-HOOD certificate, which is
-- the certificate `CrossOut` actually consumes.  It marked the cause
-- INFERRED: `refl : countFo LH.levelHoodΣ₁ ≡ 0`.
--
-- P-l says a measured cost is re-measured at its own site.  This probe
-- adds ONE declaration per run, in ascending order.
--
-- CRITERION, FIXED BEFORE THE RUNS (D-1): 20 minutes of wall time per
-- agda invocation, GHCRTS="-A64m -I0 -M8g", ONE process, cap NEVER
-- raised.
--
-- WHAT THE RUNS MEASURED, 2026-08-14, one user, one agda process:
--
--   a  `refl : countFo LH.levelHoodΣ₁ ≡ 0`              exit 0,    4 s
--   b  `eF = Cnt.erase LH.levelHoodΣ₁ cnt`              exit 0,    4 s
--   c  `eS = erase-Σ₁ ... LH.Σ₁-levelHood`              exit 0,    6 s
--   d1 `at = embed eF` at a transitive carrier          exit 0,    6 s
--   d2 `atS = mapΣ₁ Empty.rec* eS`         HEAP EXHAUSTED at 171 s, 8 GB
--   d3 the same with `{φ = eF}` given                   exit 0,    4 s
--   e  `Abs.σ₁-up atS`               WALL 20 min 1 s, RSS 9.14 GB, TERM
--   f  the same with `{φ = at}` given
--                                    WALL 20 min 1 s, RSS 9.40 GB, TERM
--
-- SO: step a is 4 seconds and [LJ-1.161]'s INFERRED cause is MEASURED
-- FALSE.  There are TWO walls, not one.
--
-- WALL 1, at `mapΣ₁`, is P-i class [F] verbatim: a lemma with an
-- IMPLICIT formula index applied at a concrete huge argument.  The cure
-- is the decision tree's first repair, one line, and NO trial preceded
-- it.  171 s of heap exhaustion becomes 4 s.
--
-- WALL 2, at `σ₁-up`, is NOT cured by [F].  It has [LJ-1.161]'s exact
-- shape: 20 minutes, about 9 GB, SIGTERM, no heap exhaustion.  It is
-- kept below as comment so the next agent reproduces it in one step.
-- INFERRED cause: `σ₁-up (σ-Δ₀ d) δ = subst ⟨_⟩ (abs₀ d δ)`
-- (src/FOL/Absoluteness.lagda.md:182-184) builds a PATH by cong₂ and
-- ⇔toPath at every node of the Δ₀ witness, and `extAtB` carries its
-- argument TWICE (src/L/Condensation.lagda.md:100-102, measured
-- generically at ProbeLJ1165A.agda), so the level-hood matrix holds the
-- twelve-row table eight times over.  That is the cost
-- src/L/Condensation/README.md:1-3 splits across three masters.
-- Do NOT raise the cap.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-165.ProbeLJ1165B {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; ∃̇_ )
open import FOL.LevyHierarchy using ( Σ₁; σ-Δ₀; σ-∃ )
open import FOL.Manipulation.Parameters using ( countFo )
open import FOL.Manipulation.Relabelling using ( mapFo; mapΔ₀; embed )
import FOL.Count
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Collapse {ℓ} using ( isTrans; module Collapse )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.BoundedSubset {ℓ} lem using ( module LevelHood; erase-Δ₀ )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Data.Vec using ( map )
import Cubical.Data.Empty as Empty

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
module CS = hPropStructure 𝒮ʟ
module Cnt = FOL.Count.Count {ℓ = ℓ-suc ℓ} CS.S

-- [LJ-1.161]'s two carriers of a Levy witness, unchanged.
mapΣ₁ : ∀ {ℓc ℓd} {K : Type ℓc} {K' : Type ℓd} (f : K → K')
        {n} {φ : Formula K n} → Σ₁ φ → Σ₁ (mapFo f φ)
mapΣ₁ f (σ-Δ₀ d) = σ-Δ₀ (mapΔ₀ f d)
mapΣ₁ f (σ-∃ s)  = σ-∃ (mapΣ₁ f s)

erase-Σ₁ : {m : ℕ} (φ : Formula CS.S m) (p : countFo φ ≡ 0)
         → Σ₁ φ → Σ₁ (Cnt.erase φ p)
erase-Σ₁ φ p (σ-Δ₀ d)    = σ-Δ₀ (erase-Δ₀ φ p d)
erase-Σ₁ (∃̇ φ) p (σ-∃ s) = σ-∃ (erase-Σ₁ φ p s)

module _ {n : ℕ}
  (N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 : Fin (5 + n))
  (M0 M1 M2 M3 M4 M5 M6 M7 M8 M9 M10 M11 s0 s1 : Fin (7 + n)) where
  module LH = LevelHood {n} N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1
                             M0 M1 M2 M3 M4 M5 M6 M7 M8 M9 M10 M11 s0 s1

  -- STEP a.  4 s.  [LJ-1.161]'s INFERRED cause, refuted.
  cnt : countFo LH.levelHoodΣ₁ ≡ 0
  cnt = refl

  -- STEP b.  the erased formula.
  eF : Formula (⊥* {ℓ-suc ℓ}) (suc (suc (suc n)))
  eF = Cnt.erase LH.levelHoodΣ₁ cnt

  -- STEP c.  the erased Levy witness.
  eS : Σ₁ eF
  eS = erase-Σ₁ LH.levelHoodΣ₁ cnt LH.Σ₁-levelHood

  module AtImage (P : S) (Ptr : isTrans P) where
    module Abs = FOL.Absoluteness.Single 𝒮ᵥ (λ x → x ∈ˢ P) Ptr
    open Abs using ( _^_ )

    -- STEP d1.  the formula at an arbitrary transitive carrier.
    at : Formula Abs.SM (suc (suc (suc n)))
    at = embed eF

    -- STEP d3.  THE CURE.  P-i repair [F]: the formula index is
    -- implicit and huge, so it is given.  Without `{φ = eF}` this
    -- declaration exhausts an 8 GB heap in 171 s; with it, 4 s.
    atS : Σ₁ at
    atS = mapΣ₁ Empty.rec* {n = suc (suc (suc n))} {φ = eF} eS

    -- STEP f.  WALL 2, MEASURED, NOT CURED.  Uncomment and run.
    -- Two runs, both under the fixed criterion, both SIGTERM at
    -- 20 min 1 s with NO heap exhaustion: 9.14 GB without the index,
    -- 9.40 GB with it.  [LJ-1.161] measured 9.03 GB for the same term.
    --
    -- levelhood-transfer : (γ : Abs.SM ^ suc (suc (suc n)))
    --   → ⟨ γ Abs.⊨ᵐ at ⟩ → ⟨ map fst γ Abs.⊨ᵛ at ⟩
    -- levelhood-transfer = Abs.σ₁-up {n = suc (suc (suc n))} {φ = at} atS

  -- The site: the collapse image is transitive, so the block above
  -- applies at the real site of [LJ-1.7].
  module AtSite (M : S) where
    module C = Collapse M
    module Image = AtImage C.πX C.πX-trans

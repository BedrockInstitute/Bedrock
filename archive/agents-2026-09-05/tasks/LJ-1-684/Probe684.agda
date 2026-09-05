{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.684] PROBE.  Adequacy at GraphB.graphBndAt, taking
-- [LJ-1.681]'s bridge as a HYPOTHESIS.  Lands nothing in src/.
--
--   THE OBLIGATION  adequacy-bnd.  v ≡ Lset γ and IsOrd give
--                   LsetGraphAt by the delivered Lset-defines
--                   (src/L/Hierarchy.lagda.md:646-648).  The
--                   hypothesized bridge, DOWN, carries that to
--                   graphBndAt.  UP is already Graph.up
--                   (ProbeLJ1162A.agda:218-222) and is not rebuilt.
--
--   NOT INHABITED   ApproxInK (532 FALSE, Probe532.agda:206-209),
--                   sat-at-level (666 NO-GO), sound-at-arity4
--                   (669 NO-GO), hoodsound-at-levelhood0 (661 NO-GO).
--                   HierInK (Probe532.agda:274-277) is 681's debt.
--
-- ONE Agda process per run, GHCRTS wide caliber, set on the pane by
-- the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-684.Probe684 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; Lset; IsOrd )
open import L.Coding.Sequence {ℓ} lem using ( LsetGraphAt )
open import L.Hierarchy {ℓ} lem using ( Lset-defines )
open import L.Condensation {ℓ} lem using ( module GraphB )
open import Cubical.Data.Vec using ( lookup )
open import Cubical.Data.Nat using ( _+_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- =====================================================================
-- W2.  GraphB is already generic in the two leaves
-- (src/L/Condensation.lagda.md:2486-2493).  Lset-defines is already
-- generic in n, w, b (src/L/Hierarchy.lagda.md:645-648).  This file
-- instantiates both.  It does not rewrite them.  It does not fix
-- n = 0.  It does not instantiate the leaves at DefBodyB; that is
-- LevelHood's instance (src/L/BoundedSubset.lagda.md:81-105) and a
-- later consumer.
--
-- P-l.  The type names GraphB.graphBndAt at GENERIC leaves, so the
-- twelve-row table does not unfold.  Floor measured that frame at
-- 2.40 s, 608,894,976 bytes, designed hole only (runs/floor-1.out).
-- =====================================================================

module Pin {m : ℕ}
  (ψs : Formula S (suc (suc (suc (5 + m)))))
  (ψa : Formula S (suc (suc (suc (7 + m)))))
  (w b K : Fin m) where

  module G = GraphB {m} ψs ψa w b K

  -- [LJ-1.681]'s bridge, the direction this consumer spends.
  -- Reverse of Graph.up (ProbeLJ1162A.agda:218-222).  Hypothesis.
  -- A BARE ∀K form is false if K may be empty; this is at ONE
  -- environment, K a slot, which is the 681 brief's wording.
  Bridge : Type (ℓ-suc ℓ)
  Bridge = (γ : S ^ m)
         → ⟨ γ ⊨ LsetGraphAt w b ⟩
         → ⟨ γ ⊨ G.graphBndAt ⟩

  -- W3.  The value equation is consumed by Lset-defines at the
  -- UNBOUNDED graph.  The bound is the hypothesized bridge.  The
  -- equation is not rewritten and does not mention K.
  adequacy-bnd-at :
    Bridge
    → (γ : S ^ m)
    → IsOrd (fst (lookup b γ))
    → fst (lookup w γ) ≡ Lset (fst (lookup b γ))
    → ⟨ γ ⊨ G.graphBndAt ⟩
  adequacy-bnd-at br γ ob q = br γ (Lset-defines w b γ ob q)

-- =====================================================================
-- THE OBLIGATION.  Lifted out of the parameterised module so the
-- witness meter can read the name (scripts/pod/witness.py:278;
-- measured on [LJ-1.651] Probe651.agda:152-156).
-- =====================================================================

adequacy-bnd = Pin.adequacy-bnd-at

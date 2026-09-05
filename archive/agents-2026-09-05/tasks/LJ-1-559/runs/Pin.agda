{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.559]  THE TYPE, PINNED.  [LJ-1.537]'s discipline
-- (agents/tasks/LJ-1-537/runs/Pin.agda), applied to this obligation.
--
-- Probe559 states its conjunct through an abbreviation, `DomAtOf`.  An
-- abbreviation can drift from the brief.  This file names NO
-- abbreviation of Probe559: it reads the type out of `InjCode` itself,
-- by projecting the second component (src/L/Cardinal.lagda.md:223-228),
-- and it inhabits that same type by `P559.domAt-at-carve` and by
-- nothing else.  If the two were different types this file would not
-- typecheck.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-559.runs.Pin {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; IsOrd )
open import L.Cardinal {ℓ} lem using ( InjCode )
open import L.Coding.Model {ℓ} using ( domAt )
open import Cubical.Data.FinData using ( Fin; zero; suc )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )

import LJ-1-521.Probe521 {ℓ} lem as P521
import LJ-1-559.Probe559 {ℓ} lem as P559

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- 1.  THE SLOT.  `InjCode`'s SECOND component, at the carve, taken by
--     projection and not by retyping.  This fixes the type without this
--     file ever writing it.
slot2 : (a b : S) (oa : IsOrd (fst a))
      → InjCode (P559.Carve.G a oa) a b
      → ⟨ (P559.Carve.G a oa ∷ a ∷ []) ⊨ domAt zero (suc zero) ⟩
slot2 a b oa h = h .snd .fst

-- 2.  THE OBLIGATION INHABITS THAT SLOT'S TYPE.  Written out here in
--     full, with no `DomAtOf`, and inhabited by the delivered term.
built : (a : S) (oa : IsOrd (fst a))
      → ⟨ (P559.Carve.G a oa ∷ a ∷ []) ⊨ domAt zero (suc zero) ⟩
built = P559.domAt-at-carve

-- 3.  AND IT IS NOT THE VACUOUS ONE.  The carve holds a real entry at
--     every member of `a`, so the domain clause is not true merely
--     because both sides are empty.
nonvacuous :
    (a : S) (oa : IsOrd (fst a)) (x : S) (xa : ⟨ fst x ∈ fst a ⟩)
  → ⟨ pr (fst x) (fst (P521.rank-at′ a oa x xa))
      ∈ fst (P559.Carve.G a oa) ⟩
nonvacuous = P559.carve-holds-the-rank-pair

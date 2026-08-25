{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.639]  NEGATIVE CONTROL.  A `refl` row proves nothing until you
-- know it can FAIL.  This file is Probe639's Section 2 with the family
-- deliberately WRONG: the target is `fst a` in place of `fst (κL a oa)`,
-- so it says the residue is the untruncation of a self-injection.  It
-- is EXPECTED to exit 42.  If it ever went green, Section 2 of
-- Probe639.agda would be measuring nothing and the report would be
-- false.  Nothing else in the file differs from the probe's Sections
-- 0 to 2.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import L.Constructible using ( IsOrd )

module LJ-1-639.runs.Control {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( ω )
open import FOL.ZFStructure using ( module hPropStructure )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.Ordinal {ℓ} using ( ω-ord )
open import L.Cardinal {ℓ} lem using ( _↪_ )
open import L.SquareLawClosed {ℓ} lem ω ω-ord using ( κL )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open hPropStructure 𝒮ʟ using ( S )

import LJ-1-618.Probe618

module P618 = LJ-1-618.Probe618 lem

UnTrunc : ((a : S) → IsOrd (fst a) → Type ℓ) → Type (ℓ-suc ℓ)
UnTrunc T = (a : S) (oa : IsOrd (fst a)) → ∥ T a oa ∥₁ → T a oa

-- THE WRONG FAMILY.  `fst a` where the probe has `fst (κL a oa)`.
SelfInj : (a : S) → IsOrd (fst a) → Type ℓ
SelfInj a oa = ⟪ fst a ⟫ ↪ ⟪ fst a ⟫

-- EXPECTED RED.
control-must-fail : P618.Inj-extract ≡ UnTrunc SelfInj
control-must-fail = refl

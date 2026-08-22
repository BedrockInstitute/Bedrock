{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.562] W3.  THE WIDEST UNMEASURED TERM: the constant list of the
-- ACTUAL formula, enumerated.  TYPE ONLY.  Written and typechecked
-- ALONE, before Probe562.agda existed.
--
-- The brief warns that 664 (agents/tasks/LJ-1-514/lj-1.514-report.md,
-- `## THE CONSTANT CENSUS`) is the carrier's count and not this
-- formula's, and orders this file to say the number for THIS formula.
-- Nothing below carries 664 into any reasoning.
--
-- THE FORMULA IS RECONSTRUCTIBLE, AND IT IS NOT RESTATED HERE.
-- [LJ-1.536]'s private form is agents/tasks/LJ-1-536/Probe536.agda:213
--
--     φ = (var zero ∈̇ con mₕ) ∨̇ (var zero ≐ con mQ)
--
-- and that task's OWN W3 already carries it at the class carrier as
-- `adjoin` (agents/tasks/LJ-1-536/runs/W3.agda:153-154).  It is
-- IMPORTED, not copied, so nothing here can drift from what that task
-- typechecked (the audit's F1/F3 rule, dev/pod/audit-2026-08-20.md).
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-562.runs.W3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import FOL.Manipulation.Parameters using ( countFo; constantsFo )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import LJ-1-536.runs.W3 {ℓ} lem using ( adjoin )

open hPropStructure 𝒮ʟ


-- ===================================================================
-- THE COUNT.  `countFo` is the tree's own counter
-- (src/FOL/Manipulation/Parameters.lagda.md:74).  The number is
-- MEASURED by `refl` and not read off the syntax by eye.
-- ===================================================================

the-formula : (h q : S) → Formula S 1
the-formula = adjoin

count : (h q : S) → countFo (the-formula h q) ≡ 2
count h q = refl


-- ===================================================================
-- THE ENUMERATION.  `constantsFo`
-- (src/FOL/Manipulation/Parameters.lagda.md:105) returns the
-- occurrences left to right, and the vector's LENGTH is the count
-- above, so this row is typeable only because that row holds.
--
-- SO THE CONSTANTS ARE NAMED AND NOT MERELY COUNTED: they are the two
-- the caller supplied, in that order, and there is no third.
-- ===================================================================

enumerated : (h q : S) → constantsFo (the-formula h q) ≡ h ∷ q ∷ []
enumerated h q = refl

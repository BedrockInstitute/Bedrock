{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.152] Probe B.  WHAT DOES ONE `hasSeparationL` COST?
--
-- Probe A measured the import load of this exact stack.  This file adds
-- ONE `hasSeparationL` instance and NOTHING else, so the difference is
-- the price of one separation at this site.
--
-- WHY THIS DECIDES THE TASK.  [LJ-1.136] section 17.5 proposed composing
-- two L-graphs "by separation over a product already in L", to avoid a
-- second `hasReplacementL`.  If separation costs what replacement costs,
-- that cure buys nothing and the brief's GO is unreachable on seconds,
-- whatever the mathematics says.  So separation is priced FIRST, alone,
-- before any composition is written.  D-1: cheapest decisive step.
--
-- ABORT CRITERION, fixed BEFORE the run:
--   CONTINUE  one separation costs under about 30 s.  Then a composition
--             built on separation can meet the brief's "nearer 3.51 than
--             254" and Probe C is worth writing.
--   NO-GO     one separation costs on the order of the 250 s replacement.
--             Then composition by separation is not a cure, and the task
--             answers NO-GO on seconds with a 30-line file.
--
-- Tracked probe; ONE agda process under GHCRTS="-A64m -I0 -M8g";
-- never committed to src/.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-152.ProbeLJ1152B {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _≐_ )
import FOL.Absoluteness
import FOL.ZFModel
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Axioms.Full {ℓ} lem using ( hasSeparationL )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module ModelL = FOL.ZFModel 𝒮ʟ
open ModelL using ( SetOf )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

-- ---------------------------------------------------------------------
-- ONE separation, at an arbitrary L-set and the cheapest formula.
-- The set is a PARAMETER, so P-l holds: no type here names a transparent
-- presentation.
-- ---------------------------------------------------------------------

module OneSep (a : S) where

  φ : Formula S 1
  φ = var zero ≐ var zero

  sep : isContr (SetOf (λ x → (x ∈ˢ a) ⊓ ((x ∷ []) ⊨ φ)))
  sep = hasSeparationL a φ

  -- Forced out of the contractible type, so the instance elaborates.
  Sep : S
  Sep = fst (fst sep)

  Sep-spec : (z : S) → (z ∈ˢ Sep) ≡ ((z ∈ˢ a) ⊓ ((z ∷ []) ⊨ φ))
  Sep-spec = snd (fst sep)

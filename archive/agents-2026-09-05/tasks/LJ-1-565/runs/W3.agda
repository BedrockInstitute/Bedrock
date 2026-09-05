{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.565] W3.  THE WIDEST UNMEASURED TERM: `AtStage` applied at
-- [LJ-1.536]'s own formula, with BOTH hypotheses supplied.  TYPE ONLY.
-- Written and typechecked ALONE, before Probe565.agda existed.
--
-- The brief orders exactly this and states the stake: "If it will not
-- apply even with both hypotheses in hand, [LJ-1.562]'s finding does
-- not reach this site and you say so at once."
--
-- NOTHING IS COPIED.  The formula, its `Δ₀` witness and its bound are
-- IMPORTED from [LJ-1.536]'s own W3 (the audit's F1/F3 rule,
-- dev/pod/audit-2026-08-20.md), so no row here can drift from what
-- that task typechecked.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-565.runs.W3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import FOL.LevyHierarchy using ( Δ₀ )
open import FOL.Manipulation.Bounding using ( BoundedFo )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; 𝒟ₒ; 𝒟ₒ-intro )
open import L.Axioms.Separation {ℓ} lem using ( module AtStage )
open import LJ-1-536.runs.W3 {ℓ} lem
  using ( adjoin; Δ₀-adjoin; Below-adjoin )

open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using () renaming ( _⊨ᵐ_ to _⊨_ )


-- ===================================================================
-- 1.  IT APPLIES.  `AtStage` at [LJ-1.536]'s formula, BOTH HYPOTHESES
--     FED, and the result is the carved set inside the stage's
--     definable powerset.
--
-- The two hypotheses are exactly the ones the stop named:
--   `Δ₀-adjoin`   agents/tasks/LJ-1-536/runs/W3.agda:156-157
--   `Below-adjoin` agents/tasks/LJ-1-536/runs/W3.agda:162-163
-- Both were typechecked by [LJ-1.536] itself and neither was reported.
-- ===================================================================

module Applied (σ : V ℓ) (oσ : IsOrd σ) where
  open AtStage σ oσ

  -- The bound, at this formula, from [LJ-1.536]'s own row.
  bound : (h q : S) → Below h → Below q → BoundedFo Below (adjoin h q)
  bound = Below-adjoin σ oσ

  -- The grade, at this formula, from [LJ-1.536]'s own row.
  grade : (h q : S) → Δ₀ (adjoin h q)
  grade = Δ₀-adjoin

  -- BOTH FED.  The formula reaches the stage's own syntax.
  lifted : (h q : S) (hh : Below h) (hq : Below q) → Formula ⟪ Lset σ ⟫ 1
  lifted h q hh hq = RL.liftFo (adjoin h q) (bound h q hh hq)

  -- AND THE CARVED SET IS IN THE DEFINABLE POWERSET OF THE STAGE.
  -- This is the row the brief asks for: `AtStage` DOES apply here.
  applied : (h q : S) (hh : Below h) (hq : Below q)
          → ⟨ carve (lifted h q hh hq) ∈ 𝒟ₒ (Lset σ) ⟩
  applied h q hh hq = carve∈𝒟ₒ (lifted h q hh hq)

  -- And the two satisfaction directions, both hypotheses fed.
  in-dir : (h q : S) (hh : Below h) (hq : Below q)
           (m : ⟪ Lset σ ⟫) (xL : ⟨ isL (⟪ Lset σ ⟫↪ m) ⟩)
         → ⟨ ((⟪ Lset σ ⟫↪ m , xL) ∷ []) ⊨ adjoin h q ⟩
         → ⟨ ⟪ Lset σ ⟫↪ m ∈ carve (lifted h q hh hq) ⟩
  in-dir h q hh hq = imageIn (adjoin h q) (bound h q hh hq) (grade h q)

  out-dir : (h q : S) (hh : Below h) (hq : Below q)
            (m : ⟪ Lset σ ⟫) (xL : ⟨ isL (⟪ Lset σ ⟫↪ m) ⟩)
          → ⟨ ⟪ Lset σ ⟫↪ m ∈ carve (lifted h q hh hq) ⟩
          → ⟨ ((⟪ Lset σ ⟫↪ m , xL) ∷ []) ⊨ adjoin h q ⟩
  out-dir h q hh hq = imageOut (adjoin h q) (bound h q hh hq) (grade h q)


-- ===================================================================
-- 2.  AND THE FINDING THE BRIEF DID NOT ASK FOR, WHICH IS THE ONE
--     THAT MATTERS: THE DOOR NEVER WANTED EITHER HYPOTHESIS.
--
-- `carve∈𝒟ₒ` (src/L/Axioms/Separation.lagda.md:211-212) takes a
-- formula at ⟪ Lset σ ⟫ and NOTHING ELSE.  No `Δ₀`, no `BoundedFo`.
-- The two hypotheses buy `carveSat` (:145-150), the SATISFACTION
-- BRIDGE from an EXTERNAL `Formula S 1`; they do not buy the door.
--
-- `𝒟ₒ-intro` itself (src/L/Constructible.lagda.md:301-304) is the same
-- statement without the stage packaging, and it too is unconditional.
-- ===================================================================

module DoorIsFree (σ : V ℓ) (oσ : IsOrd σ) where
  open AtStage σ oσ

  -- NO HYPOTHESIS.  Any formula at the stage's own carrier walks in.
  door-free : (ψ : Formula ⟪ Lset σ ⟫ 1) → ⟨ carve ψ ∈ 𝒟ₒ (Lset σ) ⟩
  door-free = carve∈𝒟ₒ

Door : V ℓ → V ℓ → Type (ℓ-suc ℓ)
Door A x = ∥ Σ[ φ ∈ Formula ⟪ A ⟫ 1 ] (DefOf.defSet A φ ≡ x) ∥₁

-- The raw door, ascribed against `𝒟ₒ-intro`.  NO `Δ₀`.  NO `BoundedFo`.
-- NO restriction on the quantifiers of φ.
door-raw : (A x : V ℓ) → Door A x → ⟨ x ∈ 𝒟ₒ A ⟩
door-raw = 𝒟ₒ-intro

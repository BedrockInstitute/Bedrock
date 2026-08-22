{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.527] W3, THE WIDEST UNMEASURED TERM, WRITTEN FIRST AND ALONE.
--
-- The brief names it: "the index match, because the congruence is one
-- step only if the two formulas agree everywhere else", and the shape
-- to write is
--
--     -- suc⁴ b against sh4 b, and suc⁴ f against sh4 f, as an equality
--
-- `sh4` is PRIVATE in src/L/Coding/Sequence.lagda.md:108-110, so it
-- cannot be named from here and no equality between the two FUNCTIONS
-- can be written.  What can be written, and what decides the same
-- question, is the equality between the two FORMULAS with the index
-- slots supplied EXPLICITLY as `suc (suc (suc (suc b)))` and
-- `suc (suc (suc (suc f)))`:
--
--   * `stepFrameAt` below takes the two indices as ARGUMENTS.  It fixes
--     no relation between them and `b`, `f`.
--   * `bodyB-at` supplies `suc⁴ b` and `suc⁴ f` and matches
--     `StepB.bodyB` (src/L/Condensation.lagda.md:2404-2408), which is
--     written with those numerals literally.
--   * `stepBody-at` supplies THE SAME two indices and matches
--     `StepBody` (src/L/Coding/Sequence.lagda.md:112-116), which is
--     written with `sh4`.
--
-- So `stepBody-at` holds by `refl` exactly when `sh4 i` computes to
-- `suc (suc (suc (suc i)))`, at both slots.  If it does not, the two
-- formulas differ in more than the leaf slot and row two is not one
-- congruence.
--
-- This file proves NOTHING about satisfaction and imports no
-- predecessor probe.  It compares two pieces of syntax.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-527.runs.W3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _∈̇_; _∧̇_ )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.Coding.Model {ℓ} using ( appAt )
open import L.Coding.Powerset {ℓ} lem using ( DefAt )
open import L.Coding.Sequence {ℓ} lem using ( StepBody )
open import L.Condensation {ℓ} lem using ( module StepB )

open import Cubical.Data.Nat using ( _+_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

-- The step frame, with the two index slots OPEN.  Everything except
-- the leaf and those two indices is written once here.
stepFrameAt : ∀ {m} (B F : Fin (4 + m))
            → Formula S (4 + m) → Formula S (4 + m)
stepFrameAt B F leaf =
  (var (suc (suc zero)) ∈̇ var B)
  ∧̇ ( appAt F (suc (suc zero)) (suc zero)
     ∧̇ ( leaf ∧̇ (var (suc (suc (suc zero))) ∈̇ var zero) ) )

-- THE BOUNDED SIDE, at suc⁴ b and suc⁴ f.
bodyB-at :
    ∀ {m} (ψ : Formula S (suc (suc (suc (4 + m))))) (v b f K : Fin m)
  → StepB.bodyB {m} ψ v b f K
    ≡ stepFrameAt (suc (suc (suc (suc b)))) (suc (suc (suc (suc f))))
        (StepB.leafB {m} ψ v b f K)
bodyB-at ψ v b f K = refl

-- THE MACHINE'S SIDE, at THE SAME suc⁴ b and suc⁴ f.  This is the
-- equality the brief ordered: it holds only if `sh4` is suc⁴.
stepBody-at :
    ∀ {m} (b f : Fin m)
  → StepBody b f
    ≡ stepFrameAt (suc (suc (suc (suc b)))) (suc (suc (suc (suc f))))
        (DefAt zero (suc zero))
stepBody-at b f = refl

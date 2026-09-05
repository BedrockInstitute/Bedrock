{-# OPTIONS --cubical --safe --guardedness #-}

-- LJ-1.368 control A.  EXPECTED RED.  It lands nothing.  Repair it never.
--
-- THE TAUTOLOGY CONTROL for `[LJ-1.365]`'s SoloC2.agda:24-27.
--
-- The motive here IS a proposition: `x ≡ y` for `x y : ⟪ δ ⟫`, and
-- `⟪ δ ⟫` is a set.  `Probe368.agda`'s `path-motive-ok` closes the SAME
-- term green with `carrier-set δ x y` as the eliminator's proof
-- argument.  Only the proof argument changes below, from the real
-- `isProp` to `squash₁`.  It is refused.
--
-- So an exit 42 on `PT.rec squash₁ ...` measures that the motive is not
-- literally a `∥ _ ∥₁`.  It does not measure the motive's h-level, and
-- it cannot support「the goal is not a proposition」.
--
-- `Probe368.agda`'s `squash-serves-∈ˢ` is the same point from the other
-- side, green: `squash₁` serves the motive `⟨ δ ∈ˢ ω ⟩`, because that
-- hProp unfolds to a truncation.

open import Base.Prelude
open import Base.Classical using ( LEM )

module LJ-1-368.MustFail368A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Ordinal.SquareLaw {ℓ} lem using ( sq )

open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; squash₁ )

open hPropStructure 𝒮ᵥ using ( S )

-- CONTROL A, SOLO.  A propositional motive, `squash₁` as its proof.
squash-at-a-path : (δ : S) (x y : ⟪ δ ⟫) → (body : sq δ → x ≡ y)
                 → ∥ sq δ ∥₁ → x ≡ y
squash-at-a-path δ x y body = PT.rec {P = x ≡ y} squash₁ body

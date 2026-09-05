{-# OPTIONS --cubical --safe --guardedness #-}

-- LJ-1.365 probe C, THE NEGATIVE CONTROLS.  EXPECTED RED.  Repair none.
-- It lands nothing.  It runs in agents/tasks/LJ-1-365/.
--
--   Probe A measured that the top wrap TYPES at the trophy's real
--   conclusion.  Three controls measure where the SAME wrap refuses.
--   Each refusal was run SOLO, in SoloC2.agda, SoloC3.agda and this file,
--   because Agda prints only the first error of a red file.  Every
--   refusal below is Agda's own output, with its run in section 4 of the
--   report.
--
--   CONTROL 1, the per-use wrap at the counting's own use.  The law's
--   first component is consumed as a FUNCTION: `Bound` pairs through it
--   at src/L/StageCardinal.lagda.md:72-73, `pair x y = fst pairing
--   (x , y)`, and the pairing parameter is `sq α` itself at `:283`.  The
--   use's goal is a value of `⟪ β ⟫`, which is not a proposition.
--   MEASURED, this file, exit 42:
--     error: [UnequalTerms]  ... !=< ∥ _A_19 ∥₁
--     when checking that the expression squash₁ has type isProp ⟪ β ⟫
--
--   CONTROL 2, the wrap at the body's first data goal, one level below
--   the trophy.  The conclusion's truncation is witnessed with injection
--   data, and the same `PT.rec` that serves the conclusion refuses
--   there.  This is the control that makes probe A's green non-vacuous.
--   MEASURED, SoloC2.agda, exit 42:
--     error: [UnequalTerms]
--     (Σ (⟪ Lset α ⟫ → ⟪ α ⟫)
--      (λ f → (x y : ⟪ Lset α ⟫) → f x ≡ f y → x ≡ y))
--     !=< ∥ _A_21 ∥₁
--     when checking that the expression squash₁ has type
--     isProp (⟪ Lset α ⟫ ↪ ⟪ α ⟫)
--
--   CONTROL 3, the delivered consumer fed the truncated band, end to
--   end.  `body-demand` (probe A) takes `[LJ-1.337]`'s `LimitBand`;
--   `[LJ-1.332]` delivers the truncated shape.  MEASURED, SoloC3.agda,
--   exit 42:
--     error: [UnequalTerms]
--     ∥ sq δ ∥₁ !=<
--     (Σ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫)
--      (λ f → (x y : ⟪ δ ⟫ × ⟪ δ ⟫) → f x ≡ f y → x ≡ y))
--     when checking that the expression t has type
--     LJ-1-337.ProbeLJ1337B.LimitBand lem

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-365.ProbeLJ1365C {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; Lset )
open import L.Ordinal.SquareLaw {ℓ} lem using ( sq )
open import L.Cardinal {ℓ} lem using ( _↪_ )

open import LJ-1-365.ProbeLJ1365A {ℓ} lem using ( LimitBandT )
open import LJ-1-337.ProbeLJ1337D {ℓ} lem using ( stage-card-from-band )

open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( ω )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( S; _∈ˢ_ )

-- CONTROL 1.  The per-use wrap, at the counting's own use of the law.
--   The motive is written out, so the refusal names the use's goal type.
per-use-wrap : (β : S) → ∥ sq β ∥₁ → ⟪ β ⟫ → ⟪ β ⟫ → ⟪ β ⟫
per-use-wrap β h x y =
  PT.rec {P = ⟪ β ⟫} squash₁ (λ p → fst p (x , y)) h

-- CONTROL 2.  The wrap at the body's first data goal.
wrap-at-injection : (α : S) → (body : sq α → ⟪ Lset α ⟫ ↪ ⟪ α ⟫)
                  → ∥ sq α ∥₁ → ⟪ Lset α ⟫ ↪ ⟪ α ⟫
wrap-at-injection α body =
  PT.rec {P = ⟪ Lset α ⟫ ↪ ⟪ α ⟫} squash₁ body

-- CONTROL 3.  The delivered consumer, fed the truncated band.
band-refusal : (α : S) (oα : IsOrd α) → LimitBandT
             → (⟨ α ∈ˢ ω ⟩ → Empty.⊥) → ⟪ Lset α ⟫ ↪ ⟪ α ⟫
band-refusal α oα t = stage-card-from-band α oα t

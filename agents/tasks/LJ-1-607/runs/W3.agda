{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.607]  W3.  THE WIDEST UNMEASURED TERM: the data payload under
-- the band's truncation, WRITTEN OUT, TYPE ONLY.  Written FIRST and
-- typechecked ALONE, per the brief, cap 120 s.
--
-- The brief: "the data payload under the band's truncation, written
-- out, TYPE ONLY.  You cannot untruncate what you have not written
-- down."
--
-- The band's truncated supply (`sq-trunc-closed`,
-- src/L/SquareLawClosed.lagda.md:325-328) holds, at every site δ of
-- the band, the truncation of the law chapter's fiber `sq δ`
-- (src/L/Ordinal/SquareLaw.lagda.md:685-687).  Written out under the
-- truncation sign, that payload is ONE function on the pairs of the
-- members of δ, and ONE injectivity proof of it.  NO Formula, no
-- L-set, no satisfaction, no code: the two components are the whole
-- payload.  That is the term this file writes down, and the two rows
-- below prove the transcription is right by `refl` at both grains.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open import L.Constructible using ( IsOrd )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )

open import LJ-1-594.runs.W3 using ( SqParam )

module LJ-1-607.runs.W3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
  (α₀ : V ℓ) (oα₀ : IsOrd α₀) where

  open import FOL.ZFStructure using ( module hPropStructure )
  open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
  open hPropStructure 𝒮ᵥ using ( S; _∈ˢ_ )
  open InfinitySet {ℓ} using ( sucV; ω )
  open import L.Ordinal.SquareLaw {ℓ} lem using ( sq )

  -- W3.1  THE PAYLOAD, WRITTEN OUT.  Under the truncation sign: one
  --        pairing function on ⟪ δ ⟫ × ⟪ δ ⟫, and one injectivity
  --        proof.  Nothing else is in the fiber.
  Payload : V ℓ → Type ℓ
  Payload δ =
    ∥ Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
         ((x y : ⟪ δ ⟫ × ⟪ δ ⟫) → f x ≡ f y → x ≡ y) ∥₁

  -- W3.2  THE TRANSCRIPTION IS RIGHT: the written-out payload IS the
  --        truncated fiber the band supply holds, by `refl`.
  payload-is-the-truncation : (δ : V ℓ) → Payload δ ≡ ∥ sq δ ∥₁
  payload-is-the-truncation δ = refl

  -- W3.3  THE OBLIGATION'S OWN TYPE, at the written-out payload: the
  --        untruncation of the whole band, from the family of
  --        truncated payloads to the untruncated product.  This is
  --        [LJ-1.605]'s `missing-direction-type`
  --        (agents/tasks/LJ-1-605/Probe605.agda:177-181) with the
  --        payload written out under the sign.
  Untruncation : Type (ℓ-suc ℓ)
  Untruncation =
      ((δ : V ℓ) → ⟨ δ ∈ˢ sucV α₀ ⟩
        → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥) → Payload δ)
    → SqParam α₀

  -- W3.4  AND IT IS THE MISSING DIRECTION, not a paraphrase of it.
  untruncation-is-the-missing-direction : Untruncation
    ≡ (((δ : V ℓ) → ⟨ δ ∈ˢ sucV α₀ ⟩
         → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥) → ∥ sq δ ∥₁)
        → SqParam α₀)
  untruncation-is-the-missing-direction = refl

  -- WHAT W3 READS OFF THE TYPE, and the probe's section 1 prices:
  -- the payload's two components are AMBIENT (a function between the
  -- member types, and a proof about it).  The truncation sits over
  -- ambient function data.  No code, no Formula and no L-set occurs
  -- anywhere in the payload, so no property of a CODED notion is
  -- available to it for free.  That is the whole question.

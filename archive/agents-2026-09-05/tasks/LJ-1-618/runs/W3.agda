{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.618]  W3.  THE WIDEST UNMEASURED TERM, as the brief states it:
-- "any existing pairing at ONE infinite ordinal, re-ascribed as a Σ,
-- TYPE ONLY".  This file is that, and nothing else.  It is written
-- FIRST and typechecked ALONE under a cap this task sets at TWO
-- MINUTES (runs/w3-1.out).
--
-- THE SEARCH, DONE BY GREP BEFORE THIS FILE.  The Σ payload the brief
-- writes is already a named type former in the tree: `sq`
-- (src/L/Ordinal/SquareLaw.lagda.md:685-687).  Two delivered terms
-- carry it at ONE ordinal each:
--   * `squareω : sq ω` (src/L/InjChain.lagda.md:184-185), at ω;
--   * `via-col-square : (α : S) → Init α → sq α`
--     (src/L/Ordinal/SquareLaw.lagda.md:960-961), at every ordinal
--     that carries `Init` (src/L/Ordinal/SquareLaw.lagda.md:692-698).
-- Nothing else in src/ types a pairing at one ordinal; the other two
-- sites of the payload shape are the BAND parameter
-- (src/L/StageCardinal.lagda.md:17-20, src/L/BoundedSubset.lagda.md:
-- 1388-1391) and the truncated closure over the band
-- (src/L/SquareLawClosed.lagda.md:325-328), and neither is one α.
--
-- ω IS AN INFINITE ORDINAL, so `squareω` reaches one infinite ordinal
-- in the brief's sense (`⟨ ω ∈ˢ ω ⟩` is refuted by ∈-irrefl, and
-- `ω-ord` is IsOrd).  `Init α` carries `⟨ ω ∈ˢ α ⟩`
-- (src/L/Ordinal/SquareLaw.lagda.md:694), so every `Init` ordinal is
-- infinite too, and `via-col-square` reaches each of them, one at a
-- time, with NO band and NO uniformity.
--
-- CALIBER.  THE PROGRAM SET GHCRTS ON THIS PANE.  I DID NOT SET IT.
-- ONE AGDA PROCESS AT A TIME.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )

module LJ-1-618.runs.W3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( ω )
open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import L.Constructible {ℓ} using ( IsOrd )
open import L.Ordinal {ℓ} using ( ω-ord )
open import L.Ordinal.SquareLaw {ℓ} lem using ( sq; Init; via-col-square )
open import L.InjChain {ℓ} lem using ( squareω )
open import Cubical.Data.Sigma using ( Σ-syntax )
import Cubical.Data.Empty as Empty


open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )

-- The brief's Σ, spelled VERBATIM, at one α.
PairingAt : V ℓ → Type ℓ
PairingAt α = Σ[ f ∈ (⟪ α ⟫ × ⟪ α ⟫ → ⟪ α ⟫) ]
                ((x y : ⟪ α ⟫ × ⟪ α ⟫) → f x ≡ f y → x ≡ y)

-- And it is the tree's own type former, by one delta step.
PairingAt-is-sq : PairingAt ≡ sq
PairingAt-is-sq = refl

-- CANDIDATE 1, at ω.  Re-ascribed at the brief's Σ.
w3-at-ω : PairingAt ω
w3-at-ω = squareω

w3-at-ω-is : w3-at-ω ≡ squareω
w3-at-ω-is = refl

-- CANDIDATE 2, at every Init ordinal, one at a time.  Re-ascribed at
-- the brief's Σ.  `Init` demands ω as a STRICT member
-- (src/L/Ordinal/SquareLaw.lagda.md:694), so this row does NOT reach
-- ω itself and does NOT reach a non-initial ordinal.
w3-at-init : (α : V ℓ) → Init α → PairingAt α
w3-at-init α iα = via-col-square α iα

w3-at-init-is : w3-at-init ≡ via-col-square
w3-at-init-is = refl

-- ω is infinite: ω is not a member of itself.
w3-ω-infinite : (⟨ ω ∈ˢ ω ⟩ → Empty.⊥)
w3-ω-infinite h = ∈-irrefl ω h

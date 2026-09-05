-- [LJ-1.505] W3 ALONE, split out so the length can be timed by itself.
-- Same text as `W3` in ../Probe505.agda:56-65.  Tracked evidence.
{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.505] The environment vector `γ'` at KValue's frame.
--
-- ONE obligation (AD12): `gammaPrime : S ^ (11 + 9)`, the vector a
-- `TFacts` value at KValue's frame would be stated over.  Nothing
-- lands in src/.  NO `TFacts` value is built.
--
-- THE FRAME, MEASURED BEFORE ANY AGDA (D-10).
--   `TFacts` is over `γ' : S ^ (11 + n)` with its fifteen indices in
--   `Fin (5 + n)`, and EVERY field reaches them through six `suc`s
--   (src/L/Condensation/TwelveAgree.lagda.md:131-133).  So the
--   `Fin (5 + n)` region is γ' slots 6 .. 5+(5+n), the whole tail, and
--   the six front slots are all that is left.  At n = 9 the tail is 14
--   slots, which is exactly `KValue.Kenv : S ^ 14`
--   (src/L/Condensation.lagda.md:7389-7395), so 6 + 14 = 11 + 9.
--   `lengthCheck` below is W3 and settles that arithmetic alone.
--
--   The six front slots are NOT free-floating.  `TFacts`'s consumer
--   states `γ'` as `f ∷ e ∷ d ∷ γ` with `γ : S ^ (8 + n)`
--   (src/L/Condensation.lagda.md:6971), so slots 0,1,2 are the three
--   existential witnesses of `satGraphOn` (src/L/Coding/Graph.lagda.md
--   :104-111) and slots 3,4,5 are the outer environment's own front.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide
-- caliber, set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-505.runs.ProbeW3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd )
open import FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ʟ using ( _^_ )
open import L.Condensation {ℓ} lem using ( module KValue )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; ∅ )
open InfinitySet {ℓ} using ( sucV; ω )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

-- =====================================================================
-- W3.  THE LENGTH ALONE, at junk in every front slot.
--   If `11 + 9` and `6 + 14` do not agree definitionally here, the
--   arithmetic is the finding and nothing else in this task matters.
-- =====================================================================

module W3 (lam : V ℓ) (ordλ : IsOrd lam)
  (succλ : (d : V ℓ) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ lam ⟩)
  (gam : V ℓ) (ordγ : IsOrd gam) (γ∈λ : ⟨ gam ∈ lam ⟩) where

  module KV = KValue lam ordλ succλ ∅∈λ gam ordγ γ∈λ

  -- the six front slots, appended to Kenv, at the length the record demands
  lengthCheck : (j : S) → S ^ (11 + 9)
  lengthCheck j = j ∷ j ∷ j ∷ j ∷ j ∷ j ∷ KV.Kenv


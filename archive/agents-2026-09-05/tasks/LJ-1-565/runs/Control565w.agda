{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.565] CONTROL w.  DOES THE ABSTRACT-WITNESS SUCCESSOR STEP
-- COMPOSE?  (Letters a to v are ATTEMPT 1's; this attempt continues at
-- w.  See the report's `## THE RECORD I DAMAGED`.)
--
-- Attempt 1 built four routes to the successor step and every one of
-- them walled (runs/attempt-1-review-of-stage-high.md.preserved,
-- `## What blocks it, measured`).  Every one targeted
-- `HierBelow (sucV α) (suc-ord oα)`, whose `isL` witness is COMPUTED
-- by `isL-ord` at a TRANSPARENT `sucV α`.
--
-- runs/Control565h.agda targets the witness ABSTRACT instead and is
-- exit 0 at 27.37 s.  The question this file settles is whether that
-- row is USABLE, or whether the wall simply moves to the place where
-- the witness must be supplied.
--
-- THE CLAIM UNDER TEST.  The witness is only a redex when its argument
-- is a transparent successor.  At a VARIABLE γ, `isL-ord γ oγ` is
-- stuck, so the bridge back to [LJ-1.536]'s own statement should be
-- free.  If it is, the induction can carry the witness abstract
-- throughout and pay it once, at a variable, at the end.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-565.runs.Control565w {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; IsOrd; Lset )
open import L.Hierarchy {ℓ} lem using ( hierL )
open import LJ-1-536.Probe536 {ℓ} lem
  using ( step; isL-ord; HierBelow; HierBelowAll )

open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

HierBelowH : (γ : V ℓ) → ⟨ isL γ ⟩ → IsOrd γ → Type (ℓ-suc ℓ)
HierBelowH γ hγ oγ = ⟨ fst (hierL γ hγ oγ) ∈ Lset (step 3 γ) ⟩

-- THE BRIDGE, AT A VARIABLE γ.  Nothing here is a successor, so
-- `isL-ord γ oγ` is stuck and no well-founded recursion can unfold.
bridge : (γ : V ℓ) (oγ : IsOrd γ) → HierBelowH γ (isL-ord γ oγ) oγ → HierBelow γ oγ
bridge γ oγ x = x

-- AND THE WHOLE-CLASS FORM FOLLOWS, so an induction may carry the
-- witness abstract from end to end and pay it once, here.
HierBelowAllH : Type (ℓ-suc ℓ)
HierBelowAllH = (γ : V ℓ) (h : ⟨ isL γ ⟩) (o : IsOrd γ) → HierBelowH γ h o

allH→all : HierBelowAllH → HierBelowAll
allH→all f γ oγ = bridge γ oγ (f γ (isL-ord γ oγ) oγ)

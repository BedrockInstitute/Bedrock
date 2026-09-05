{-# OPTIONS --cubical --safe --guardedness #-}

-- LJ-1.164 probe A.  REACHABILITY AFTER THE MOVE.
--
-- WHAT THIS PROBE IS FOR.  `[LJ-1.164]` moved `elem-down` and the chain
-- above it out of `module Co` and up into `BoundedSubsetAt`.  `Co`
-- takes the phase's two open hypotheses `levelIn` and `cover`, so
-- before the move nobody who was PROVING those two could name
-- `elem-down`.  The move is a placement change, and Agda decides
-- whether it is pure.  The master typechecks, so it is.
--
-- The master's own green run does NOT measure reachability.  A
-- definition stays green wherever it sits.  This probe measures the
-- thing the move was for: that `elem-down` can now be named, and
-- CONSUMED, in a scope where `levelIn` and `cover` are still open.
--
-- BLOCK 1  `elem-down` named directly on `BoundedSubsetAt`, with NO
--          application of `Co`.  Before the move this line could not
--          be written at all.
-- BLOCK 2  THE SHAPE `[LJ-1.7]` NEEDS: a proof of `levelIn` that
--          consumes `elem-down`.  This is the blocker, stated as a
--          type.  `route` supplies `elem-down` to a would-be proof of
--          `LevelIn`; before the move `elem-down` was not in scope at
--          that point, because it lived inside the module that
--          `levelIn` parameterizes.  The same for `cover`.
--
-- NO `refl` BETWEEN TWO MODULE APPLICATIONS.  `[LJ-1.163]` MEASURED a
-- wall there: 20:42.15 wall, RSS 2074 MB against an 8 GB cap, no heap
-- exhaustion.  P-i forbids surgery on a walling term, and this probe
-- does not need the identification, so it does not write it.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-164.ProbeLJ1164A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; Lset )
open import L.BoundedSubset {ℓ} lem using ( module Devlin55; IsCardinal; _↪_ )

open import Cubical.Data.Sigma using ( _×_; _,_ )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; _∪_; ⁅_⁆s; module InfinitySet )
open InfinitySet using ( ω; sucV )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- =====================================================================
-- THE SITE.  The fifteen parameters of `Devlin55.BoundedSubsetAt`,
-- copied from `src/L/BoundedSubset.lagda.md:1385-1395`.  They stay
-- OPEN: this probe discharges none of them and claims nothing about
-- them.
-- =====================================================================

module Site
  (κ : S) (ordκ : IsOrd κ) (cardκ : IsCardinal κ) (κ∉ω : ⟨ κ ∈ˢ ω ⟩ → Empty.⊥)
  (α : S) (ordα : IsOrd α) (α∈κ : ⟨ α ∈ˢ κ ⟩) (α∉ω : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
  (sq : (δ : S) → ⟨ δ ∈ˢ sucV α ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥)
      → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
          ((u v : ⟪ δ ⟫ × ⟪ δ ⟫) → f u ≡ f v → u ≡ v))
  (x : S) (x⊆Lα : (z : S) → ⟨ z ∈ˢ x ⟩ → ⟨ z ∈ˢ Lset α ⟩)
  (absorbs : ⟪ Lset α ∪ ⁅ x ⁆s ⟫ ↪ ⟪ Lset α ⟫)
  (lam : S) (ordλ : IsOrd lam) (α∈λ : ⟨ α ∈ˢ lam ⟩)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (x∈Lλ : ⟨ x ∈ˢ Lset lam ⟩) where

  module BSA = Devlin55.BoundedSubsetAt κ ordκ cardκ κ∉ω α ordα α∈κ α∉ω sq
                 x x⊆Lα absorbs lam ordλ α∈λ succλ x∈Lλ

  -- The two open hypotheses of the phase, as types.  `Co` takes them;
  -- `[LJ-1.7]` must PROVE them.
  LevelIn : Type (ℓ-suc ℓ)
  LevelIn = (δ : S) → IsOrd δ → ⟨ δ ∈ˢ BSA.HS.C.πX ⟩
          → ⟨ Lset δ ∈ˢ BSA.HS.C.πX ⟩

  Cover : Type (ℓ-suc ℓ)
  Cover = (y : S) → ⟨ y ∈ˢ BSA.HS.M ⟩
        → ∥ Σ[ γ ∈ S ] (IsOrd γ × ⟨ γ ∈ˢ BSA.HS.C.πX ⟩
                                × ⟨ BSA.HS.C.π y ∈ˢ Lset γ ⟩) ∥₁

  -- ===================================================================
  -- BLOCK 1.  `elem-down` WITHOUT `Co`.
  --
  -- `BSA.elem-down` resolves.  `Co` is NOT applied anywhere in this
  -- block, so `levelIn` and `cover` have no value here.  Before the
  -- move the only path to the supply was `(BSA.Co levelIn cover)
  -- .elem-down`, which needs both.
  -- ===================================================================

  ed : BSA.DR54.ElemDown
  ed = BSA.elem-down

  -- ===================================================================
  -- BLOCK 2.  THE SHAPE `[LJ-1.7]` NEEDS.
  --
  -- A proof of `levelIn` or of `cover` may now consume `elem-down`.
  -- The two functions below state exactly that and nothing more: they
  -- take the discharge step as a hypothesis and feed it the supply.
  -- They prove neither `LevelIn` nor `Cover`, and they claim nothing
  -- about either.  What they measure is SCOPE: `elem-down` is in scope
  -- at the point where those two are still open goals.
  -- ===================================================================

  route-levelIn : (BSA.DR54.ElemDown → LevelIn) → LevelIn
  route-levelIn k = k BSA.elem-down

  route-cover : (BSA.DR54.ElemDown → Cover) → Cover
  route-cover k = k BSA.elem-down

  -- Both hypotheses at once, which is how `Co` consumes them.
  route-both : (BSA.DR54.ElemDown → LevelIn × Cover) → LevelIn × Cover
  route-both k = k BSA.elem-down

  -- And the discharged pair still reaches `Co`, so the move costs the
  -- delivered assembly nothing: `Co` is applied here to hypotheses
  -- that were themselves produced with `elem-down` in hand.
  module Closed (k : BSA.DR54.ElemDown → LevelIn × Cover) where
    pair : LevelIn × Cover
    pair = route-both k

    module Co' = BSA.Co (pair .fst) (pair .snd)

    theorem : ⟨ x ∈ˢ Lset κ ⟩
    theorem = Co'.theorem

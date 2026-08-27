{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.701]  `param-at-omega` FROM `squareω` ALONE.
--
-- THE OBLIGATION.  `param-at-omega : SqParam ω`, built from `squareω`
-- alone.  Re-derived from [LJ-1.636]: `collapse-at-ω` is
-- agents/tasks/LJ-1-636/Probe636.agda:377-381, and `param-at-ω` is
-- :391-392, verbatim up to the obligation's ASCII name.
--
-- THIS FILE CARRIES NO HOLE AND NO POSTULATE.  Nothing lands in `src/`.
-- It BUILDS NO SQUARE LAW: the one inhabitant used, `squareω`, is
-- already in the tree (src/L/InjChain.lagda.md:184).
--
-- CALIBER.  The program set GHCRTS on this pane; I did not set it.  One
-- Agda process at a time.  The floor was measured before the proof:
-- runs/Floor.agda.txt, runs/floor-1.out.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-701.Probe701 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Model {ℓ} using ( ∈sucV-elim )
open import L.InjChain {ℓ} lem using ( squareω )

open import Cubical.Data.Sigma using ( Σ-syntax; _×_ )
import Cubical.Data.Empty as Empty
open import Cubical.HITs.CumulativeHierarchy.Base using ( setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( ω; sucV )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- The `sq` parameter's value type, copied from its binder
-- (src/L/StageCardinal.lagda.md:18-20).
Sq : S → Type ℓ
Sq δ = Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
         ((u v : ⟪ δ ⟫ × ⟪ δ ⟫) → f u ≡ f v → u ≡ v)

SqParam : S → Type (ℓ-suc ℓ)
SqParam α₀ = (δ : S) → ⟨ δ ∈ˢ sucV α₀ ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥) → Sq δ

-- W3.  `squareω` inhabits the value type AT ω, on the nose.
-- Same inhabitant, same type as agents/tasks/LJ-1-636/Probe636.agda:100-101.
delivered-at-ω : Sq ω
delivered-at-ω = squareω

-- [LJ-1.636]'s `collapse-at-ω`, Probe636.agda:377-381.  Re-derived, not
-- imported: that probe is on a SIBLING WORKTREE and is not in git.
collapse-at-ω : (δ : S) → ⟨ δ ∈ˢ sucV ω ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥) → δ ≡ ω
collapse-at-ω δ δ∈sucVω infδ =
  ∈sucV-elim {A = ω} {x = δ} (setIsSet δ ω) δ∈sucVω
    (λ δ∈ω → Empty.rec (infδ δ∈ω))
    (λ e → e)

-- THE OBLIGATION.  The brief names this ASCII identifier.  The body is
-- Probe636.agda:391-392, with `param-at-ω` renamed to `param-at-omega`.
param-at-omega : SqParam ω
param-at-omega δ δ∈suc infδ =
  subst Sq (sym (collapse-at-ω δ δ∈suc infδ)) squareω

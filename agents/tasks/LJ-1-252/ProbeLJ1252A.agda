{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.252] probe A: the `ω ∈ lam` join, measured, not read.
--
-- [LJ-1.199] stopped at ZERO lines on the claim that `ω ∈ lam` cannot
-- be supplied at `HullStage`'s telescope, and it never ran Agda.  This
-- probe measures the three claims that decide the question.
--
--  1. Countermodel  -- `lam = ω` satisfies the four hypotheses
--                      `(ordλ, succλ, ∅∈λ)` while `ω ∈ lam` is empty.
--                      So `ω ∈ lam` is NOT derivable from the
--                      telescope as it stands (branch 1 is false).
--  2. ω∈λ-from-α    -- at the actual consumer (`BoundedSubsetAt`),
--                      `α∉ω` and `α∈λ` DO give `ω ∈ lam`, five lines.
--  3. ω∈sucα        -- the `σ` the bound needs: `ω ∈ sucV α` from
--                      `α∉ω` alone, for `envSetNumeral∈` at `σ = sucV α`.
--
-- 1 is the refutation of "derivable".  2 and 3 are the consumer-side
-- price of adding the hypothesis, and they are the whole of it.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

open import FOL.ZFStructure using ( module hPropStructure )
import Cubical.Data.Empty as Empty
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; ∅ )

module LJ-1-252.ProbeLJ1252A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import V.Model {ℓ} using ( self∈sucV; ∈sucV-inl )
open import L.Constructible {ℓ} using ( IsOrd )
open import L.Ordinal {ℓ} using ( ω-ord; #∈ω )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
open InfinitySet using ( ω; sucV; ω-next )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ∈∈ₛ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- ===================================================================
-- 1. THE COUNTERMODEL.  `lam = ω` is a valid instantiation of the
-- four hypotheses a derivation of `ω ∈ lam` would have to use, and
-- there `ω ∈ lam` is `ω ∈ˢ ω`, empty by regularity.  So `∅∈λ + succλ
-- + ordλ` do not derive `ω ∈ lam`.  MEASURED.
-- ===================================================================

module Countermodel where

  ∅∈ω : ⟨ ∅ ∈ˢ ω ⟩
  ∅∈ω = #∈ω 0

  -- ω is successor-closed: the cubical library's `ω-next`, read at the
  -- structure membership.
  succω : (d : S) → ⟨ d ∈ˢ ω ⟩ → ⟨ sucV d ∈ˢ ω ⟩
  succω d d∈ω =
    ∈∈ₛ {a = sucV d} {b = ω} .snd
      (ω-next d (∈∈ₛ {a = d} {b = ω} .fst d∈ω))

  -- At `lam = ω`, `ω ∈ lam` is `ω ∈ˢ ω`.
  ω∈ω-empty : ⟨ ω ∈ˢ ω ⟩ → Empty.⊥
  ω∈ω-empty = ∈-irrefl ω

-- ===================================================================
-- 2. THE SITE DERIVATION.  The one consumer of `HullStage`
-- (`BoundedSubsetAt`, src/L/BoundedSubset.lagda.md:1405) holds
-- `α∉ω : α ∈ˢ ω → ⊥` and `α∈λ : α ∈ˢ lam`, both ordinals.  By
-- trichotomy `α ∈ˢ ω ∨ α ≡ ω ∨ ω ∈ˢ α`; the first is excluded, and
-- each survivor puts `ω` inside `lam`.  MEASURED.
-- ===================================================================

ω∈λ-from-α : (α lam : S) → IsOrd α → IsOrd lam
           → (⟨ α ∈ˢ ω ⟩ → Empty.⊥)
           → ⟨ α ∈ˢ lam ⟩
           → ⟨ ω ∈ˢ lam ⟩
ω∈λ-from-α α lam oα oλ α∉ω α∈λ = go (ord-tri α oα ω ω-ord)
  where
  go : ⟨ α ∈ˢ ω ⟩ ⊎ ((α ≡ ω) ⊎ ⟨ ω ∈ˢ α ⟩) → ⟨ ω ∈ˢ lam ⟩
  go (inl α∈ω)       = Empty.rec (α∉ω α∈ω)
  go (inr (inl α≡ω)) = subst (λ w → ⟨ w ∈ˢ lam ⟩) α≡ω α∈λ
  go (inr (inr ω∈α)) = oλ .fst ω∈α α∈λ

-- ===================================================================
-- 3. THE σ THE BOUND NEEDS.  `envSetNumeral∈` (src/L/Coding/Key.lagda.md
-- :476) wants `ω ∈ σ` where `fst B ∈ Lset σ`; with the carrier `B =
-- LsetS α`, the natural σ is `sucV α`, and `ω ∈ sucV α` follows from
-- `α∉ω` alone.  MEASURED.
-- ===================================================================

ω∈sucα : (α : S) → IsOrd α → (⟨ α ∈ˢ ω ⟩ → Empty.⊥) → ⟨ ω ∈ˢ sucV α ⟩
ω∈sucα α oα α∉ω = go (ord-tri α oα ω ω-ord)
  where
  go : ⟨ α ∈ˢ ω ⟩ ⊎ ((α ≡ ω) ⊎ ⟨ ω ∈ˢ α ⟩) → ⟨ ω ∈ˢ sucV α ⟩
  go (inl α∈ω)       = Empty.rec (α∉ω α∈ω)
  go (inr (inl α≡ω)) = subst (λ w → ⟨ w ∈ˢ sucV α ⟩) α≡ω (self∈sucV α)
  go (inr (inr ω∈α)) = ∈sucV-inl ω∈α

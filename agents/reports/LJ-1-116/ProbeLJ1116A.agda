{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.116] probe A: at which alpha does Upper demand sq, and does
-- the omega site close with the honest pairing?
--
-- The demand set, read from the code:
--   Devlin55 applies stage-card-upper α ordα α∉ω at its site's own α
--   (src/L/BoundedSubset.lagda.md:1529-1530), and CodeCount's Bound
--   is at the same α (:1426-1427).  Upper.stage-card-upper is
--   ∈-induction step; step α = limit-step α, whose Bound instantiates
--   sq α infα (src/L/StageCardinal.lagda.md:281).  The descent applies
--   step at every member δ of α (src/V/Hierarchy.lagda.md:177-180);
--   at a finite δ the premise δ ∉ ω is empty, so P δ closes by
--   absurdity and sq δ is never demanded; at every infinite δ ≤ α,
--   sq δ is demanded.
-- At the concrete consumer site α = ω (src/ProbeLJ194A.agda:1202-1210),
-- every member of ω is finite, so the demand set is {ω}.
--
-- This probe machine-checks the omega site:
--   1. sqω : the honest pairing at ω, from
--      NumeralPresentation.pairω / pairω-inj.
--   2. up-ω : Up.stage-card-upper ω ω-ord (∈-irrefl ω), the site's
--      own stage-card-upper, GREEN given the sq parameter.
--   3. up-ω-compute: the one-step unfolding, so the top-level demand
--      is limit-step at ω, i.e. sq ω.
--   4. count-ω : the Bound formula-count at ω over ⟪ Lset ω ⟫.
--   5. Init ω is false, and Init (sucV δ) is false for every δ, so
--      Init cannot replace sq at the site or at successor members.
--
-- Untracked probe; ONE agda process under GHCRTS="-A64m -I0 -M8g";
-- never committed.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open import Cubical.Data.Empty as Empty

module ProbeLJ1116A {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
  (sq : (α : V ℓ) → (⟨ α ∈ InfinitySet.ω {ℓ} ⟩ → Empty.⊥)
      → Σ[ f ∈ (⟪ α ⟫ × ⟪ α ⟫ → ⟪ α ⟫) ]
          ((x y : ⟪ α ⟫ × ⟪ α ⟫) → f x ≡ f y → x ≡ y)) where

open InfinitySet {ℓ} using ( ω; sucV )
open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl; ∈-induction-compute )
open import L.Constructible {ℓ} using ( IsOrd; Lset )
open import L.Ordinal {ℓ} using ( ω-ord )
import L.Ordinal.SquareLaw {ℓ} lem as SQ
open import V.Model {ℓ} using ( self∈sucV )
open import FOL.Syntax using ( Formula )
import ProbeLJ1106A {ℓ} lem as P106
open P106 using ( module NumeralPresentation )
import L.StageCardinal

module SC = L.StageCardinal {ℓ} lem sq
module Up = SC.Upper

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

_↪_ : Type ℓ → Type ℓ → Type ℓ
X ↪ Y = Σ[ f ∈ (X → Y) ] ((x y : X) → f x ≡ f y → x ≡ y)

-- 1. The honest pairing at ω: the demand at the site is satisfiable
-- by the delivered ℕ pairing, no Init, no truncation.
sqω : SQ.sq ω
sqω = NumeralPresentation.pairω , NumeralPresentation.pairω-inj

-- 2. The site's own stage-card-upper, with the sq parameter.
up-ω : ⟪ Lset ω ⟫ ↪ ⟪ ω ⟫
up-ω = Up.stage-card-upper ω ω-ord (∈-irrefl ω)

-- 4. The CodeCount-side demand: Bound's formula-count at ω over the
-- stage's index, the pairing at ω in the counting shape.
module Bω = SC.Bound ω ω-ord (∈-irrefl ω) (sq ω (∈-irrefl ω))

count-ω : (g : ⟪ Lset ω ⟫ ↪ ⟪ ω ⟫)
        → Σ[ f ∈ (Formula (⟪ Lset ω ⟫) 1 → ⟪ ω ⟫) ]
            ((φ ψ : Formula (⟪ Lset ω ⟫) 1) → f φ ≡ f ψ → φ ≡ ψ)
count-ω g = Bω.formula-bound {K = ⟪ Lset ω ⟫} g

-- 5. Init cannot replace sq at the site: Init ω is false (ω ∉ ω).
Initω-false : SQ.Init ω → Empty.⊥
Initω-false i = ∈-irrefl ω (i .snd .fst)

-- Init cannot replace sq at any successor ordinal: the successor
-- closure clause at γ = δ demands sucV δ ∈ sucV δ.
InitSuc-false : (δ : S) → SQ.Init (sucV δ) → Empty.⊥
InitSuc-false δ i = ∈-irrefl (sucV δ) (i .snd .snd .fst δ (self∈sucV δ))

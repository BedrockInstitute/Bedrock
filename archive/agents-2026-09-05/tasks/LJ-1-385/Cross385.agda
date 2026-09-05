{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.385] DD25 REVIEW.  THE IDENTIFICATION, MEASURED.
--
-- `[LJ-1.383]` says the six residue parameters of `[LJ-1.338]`'s leaf
-- supply are the objects five prior tasks refuted.  This file measures
-- the FIRST half of that identification and nothing else.
--
-- WHAT IS GREEN HERE.  My restatements of residue 1 (`wArNum`) and
-- residue 2 (`wUnArNum`) go into `Supply`'s two residue slots and the
-- module application typechecks.  So the two types below ARE the two
-- residue slots, by the elaborator and not by my reading.
--
-- WHAT THE RED CONTROL MEASURES.  `Cross385.agda` is this file plus ONE
-- module application: `[LJ-1.341]`'s `Refute` at `Supply`'s own
-- environment.  It is EXPECTED RED, and the refusal is the finding: the
-- refutations live at `𝒮ʟ` and the residue lives at `𝒮ᵥ ↾ Full`.
--
-- ONE agda process under GHCRTS="-A64m -I0 -M8g".

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

open import FOL.ZFStructure using ( module hPropStructure; _↾_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅ ) renaming ( module InfinitySet to Inf )
open Inf using ( #_; sucV )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

import LJ-1-338.ProbeLeaf338
import LJ-1-341.ProbeTies341

module LJ-1-385.Cross385 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( IsOrd )

import LJ-1-297.ProbeLJ1297A {ℓ} lem as P1297A
module PL = LJ-1-338.ProbeLeaf338 {ℓ} lem
module PT341 = LJ-1-341.ProbeTies341 {ℓ} lem

-- THE AMBIENT STRUCTURE.  This line is `ProbeLeaf338.agda:62`, copied.
open hPropStructure (𝒮ᵥ ↾ P1297A.Full) using ( S )

-- RESIDUE 1, restated from `ProbeLeaf338.agda:119-122`.
WArNum : Type (ℓ-suc ℓ)
WArNum = (w' : S) → (k : ℕ) → (c ar a b : S)
       → ⟨ fst c ∈ fst w' ⟩
       → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
       → ∥ Σ[ m ∈ ℕ ] (fst ar ≡ # m) ∥₁

-- RESIDUE 2, restated from `ProbeLeaf338.agda:124-127`.
WUnArNum : Type (ℓ-suc ℓ)
WUnArNum = (w' : S) → (k : ℕ) → (c ar a : S)
         → ⟨ fst c ∈ fst w' ⟩
         → fst c ≡ pr (fst ar) (pr (# k) (fst a))
         → ∥ Σ[ m ∈ ℕ ] (fst ar ≡ # m) ∥₁

module Test (lam : V ℓ) (ordλ : IsOrd lam)
            (succλ : (d : V ℓ) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩)
            (∅∈λ : ⟨ ∅ ∈ lam ⟩)
            (gam : V ℓ) (ordγ : IsOrd gam) (γ∈λ : ⟨ gam ∈ lam ⟩)
            (wArNum : WArNum) (wUnArNum : WUnArNum) where

  -- THE IDENTIFICATION, HALF ONE.  This application typechecks only if
  -- `WArNum` and `WUnArNum` above ARE the residue slots.
  module Sup = PL.Supply lam ordλ succλ ∅∈λ gam ordγ γ∈λ wArNum wUnArNum

  -- THE ONE ADDED LINE.  `[LJ-1.341]`'s `Refute` module, applied at
  -- `[LJ-1.338]`'s OWN environment and at the K slot the residue names.
  -- If this is GREEN, the identification holds by the elaborator.
  module R341 = PT341.Refute {17} (suc (suc (suc PL.K))) Sup.γ

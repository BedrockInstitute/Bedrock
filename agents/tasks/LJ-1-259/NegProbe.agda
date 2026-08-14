{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.259] negative probe: envConsK over (K, Ktr) ALONE.  The hole
-- shows the goal is a fresh `finSet` membership and that Ktr/prK supply
-- no constructor for it.  Kept as the measurement that the closure does
-- not build over (K, Ktr).  ONE agda process, GHCRTS="-A64m -I0 -M8g".

open import Base.Prelude
open import Base.Truth

module LJ-1-259.NegProbe {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; isTransV )
open import L.Axioms.Basic {ℓ} using ( finSet )
open import L.Coding.Environment {ℓ} using ( env; cons )

open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( #_; sucV )
open import Cubical.Data.Nat using ( ℕ )
open import Cubical.Data.FinData using ( Fin; toℕ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module Fact (K : S) (Ktr : isTransV (fst K)) where

  -- The closure asked for, with ONLY (K, Ktr).  The goal is
  -- `finSet (suc k) (λ j → pr (# (toℕ j)) (cons x g j)) ∈ fst K`,
  -- and no term in this telescope concludes such a membership.
  envConsK : {k : ℕ} (g : Fin k → V ℓ) (x : V ℓ)
           → ⟨ env g ∈ fst K ⟩ → ⟨ x ∈ fst K ⟩
           → ⟨ env (cons x g) ∈ fst K ⟩
  envConsK g x envgK xK = {!!}

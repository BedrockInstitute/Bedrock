{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.565] CONTROL m.  THE SUCCESSOR STEP, WITH THE SEQUENCE NAMED
-- BY A LOCAL ABBREVIATION INSTEAD OF BY [LJ-1.536]'S IMPORTED `seq`.
--
-- Control k passed the sequence to `AdjoinAt` UNABBREVIATED and hit
-- the wall; controls d, e and g passed [LJ-1.536]'s `seq` and hit it
-- too.  Controls f, i and j show that the same shapes cost 1.71 s when
-- no such step is asked for.  This file keeps the engine imported and
-- gives the sequence a LOCAL name of exactly the shape [LJ-1.536] gave
-- it, which is the one variant not yet measured.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-565.runs.Control565o {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Model {ℓ} using ( self∈sucV; ∈sucV-inl; ∈sucV-elim )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; IsOrd; Lset )
open import L.Ordinal {ℓ} using ( suc-ord )
open import L.Hierarchy {ℓ} lem using ( hierL; hierL-spec; IsHier )
open import LJ-1-536.Probe536 {ℓ} lem
  using ( step; isL-ord; HierBelow; pr-at; module AdjoinAt )

open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ


-- [LJ-1.565] CONTROL o.  THE IMPORTED ENGINE, RE-ASCRIBED AND NOTHING
-- ELSE.  No hierarchy, no successor, no stage arithmetic: only
-- [LJ-1.536]'s `AdjoinAt.adjoin∈` given its own type back.

engine : (σ : V ℓ) (oσ : IsOrd σ) (h q : V ℓ)
         (h∈ : ⟨ h ∈ Lset σ ⟩) (q∈ : ⟨ q ∈ Lset σ ⟩) (T : S)
         (out : (x : S) → (⟨ fst x ∈ h ⟩ ⊎ (fst x ≡ q))
              → ⟨ fst x ∈ fst T ⟩)
         (into : (x : S) → ⟨ fst x ∈ fst T ⟩
               → ∥ ⟨ fst x ∈ h ⟩ ⊎ (fst x ≡ q) ∥₁)
       → ⟨ fst T ∈ Lset (sucV σ) ⟩
engine = AdjoinAt.adjoin∈

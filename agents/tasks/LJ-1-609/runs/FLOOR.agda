{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.609]  FLOOR RUN.  This file's frame with the obligation at ONE
-- designed hole, run BEFORE any proof (the owner's ruling of 2026-08-23
-- and D-26): it prices what the elaboration frame itself costs, import
-- list included, before the term is written against it.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-609.runs.FLOOR {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import FOL.Count {ℓ} using ( code; shape-count-inj )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Presentation {ℓ} using ( member; ↪-inj )
open import V.Coding {ℓ} using ( pr; pr-inj; #-inj )
open import L.Constructible {ℓ}
  using ( IsOrd; Lset; Lset-in; Lset-out; Lset-mono )
open import L.Ordinal {ℓ} using ( mem-ord; suc-ord )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc; Lset-cumul )
open import L.Axioms.Basic {ℓ} using ( ∅∈𝒟ₒ; Lset-suc; pr∈Lset-suc )
open import L.BoundedSubset {ℓ} lem
  using ( module HullStage; module DownReflect; module HullElemDown )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; ∅; ∅-empty )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; ∈∈ₛ )
open InfinitySet {ℓ} using ( sucV; #_ )
open import Cubical.Data.Nat using ( ℕ )
open import Cubical.Data.Vec using ( Vec; _∷_; [] )
open import Cubical.Data.Sigma using ( Σ≡Prop; ΣPathP )
open import Cubical.Foundations.Prelude using ( toPathP )
open import Cubical.Foundations.Transport using ( substSubst⁻ )
open import Cubical.Foundations.HLevels using ( isSetΣ; isProp→isSet )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )
import LJ-1-606.Probe606 {ℓ} lem as P606

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
module SV = hPropStructure 𝒮ᵥ
open SV using ( _∈ˢ_; isSetS )

-- THE OBLIGATION, AT ONE DESIGNED HOLE.
elem-down-at :
    (lam : SV.S) (ordλ : IsOrd lam)
    (succλ : (d : SV.S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
    (X : SV.S)
    (X⊆Lλ : (z : SV.S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
    (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩)
  → P606.Frame.ElemDownAt lam ordλ succλ X X⊆Lλ ∅∈λ
elem-down-at lam ordλ succλ X X⊆Lλ ∅∈λ = {! !}

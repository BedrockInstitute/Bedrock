{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.622]  PART 1 of 4: the bridges.  Probe sections 0 to 2.
--
-- The obligation type, the one-line ordinal-to-L bridge, and the
-- truncation bridge into the ambient cardinal.  Everything here is
-- plumbing; no part of the construction lives here.
--
-- The header is the landed master's import set: the eleven modules of
-- agents/tasks/LJ-1-619/Probe619.agda:20-30, taken from
-- agents/tasks/LJ-1-528/Probe528.agda:14-60 with the two imports that
-- `[LJ-1.555]` left out with the sections that did not move
-- (L.Axioms.Infinity and L.InjChain).  Parts 2 to 4 and the top rung
-- carry the same header so that a per-part delta is never an import
-- delta.
--
-- Nothing is postulated.  Nothing lands in src/.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM; lowerLEM )

module LJ-1-622.Part1 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl; regularityV )
open import V.Presentation {ℓ} using ( member; fiber )
open import V.Model {ℓ} using ( self∈sucV )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; IsOrd; isL; isL-trans; Lset; Lset→isL; isTransV
        ; isPropIsTransV )
open import L.Ordinal {ℓ} using ( ∅-ord; ω-ord; mem-ord; suc-ord; setUnion-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.Ordinal.Linear {ℓ} lem using ( Tri; ord-tri )
open import L.Cardinal {ℓ} lem using ( IsCardinalL; InjCode )
open import L.BoundedSubset {ℓ} lem
  using ( IsCardinal; _↪_; module Devlin55 )
open import L.CantorBernstein {ℓ} lem using ( readL )

open Devlin55 using ( comp-inj; ord-emb )

open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; sett; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; _∈ₛ_; _⊆_; extensionality; isEmb⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; module SeparationSet; ⋃_; union-ax )
open InfinitySet {ℓ} using ( ω; sucV )
open import Cubical.Data.Sigma using ( _×_; Σ≡Prop )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Foundations.HLevels using ( isPropΠ; isProp×; isPropΣ )
open import Cubical.Data.Bool using ( Bool; true; false; false≢true )
open import Cubical.Induction.WellFounded
  using ( Acc; acc; WellFounded; module WFI )
open import Cubical.Functions.Embedding
  using ( isEmbedding; injEmbedding; isEmbedding→hasPropFibers
        ; Embedding-into-isSet→isSet )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))

module SV = hPropStructure 𝒮ᵥ
module SL = hPropStructure 𝒮ʟ

open SV using ( _∈ˢ_ )

-- The obligation type, at `[LJ-1.526]`'s own binding
-- (agents/tasks/LJ-1-526/Probe526.agda:178-183), re-typed at
-- agents/tasks/LJ-1-528/Probe528.agda:58-64.

CardAboveLᵀ : Type (ℓ-suc ℓ)
CardAboveLᵀ =
    (κ : SL.S) → IsOrd (fst κ) → IsCardinalL κ
  → (⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)
  → ∥ Σ[ θ ∈ SL.S ]
       (IsOrd (fst θ) × IsCardinalL θ × ⟨ fst κ ∈ˢ fst θ ⟩) ∥₁

-- An ordinal is an L-element at the stage after itself.
-- agents/tasks/LJ-1-528/Probe528.agda:76.

ordL : (x : SV.S) → IsOrd x → SL.S
ordL x ox = x , Lset→isL (sucV x) (suc-ord ox) x (ord∈Lset-suc x ox)

-- The ambient-to-internal bridge.
-- agents/tasks/LJ-1-528/Probe528.agda:88-89.

ambient→internal : (κ : SL.S) → IsCardinal (fst κ) → IsCardinalL κ
ambient→internal κ c δ δ∈κ h =
  PT.rec Empty.isProp⊥ (λ w → c (fst δ) δ∈κ (readL κ δ w)) h

{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.663]  The two semantic laws [LJ-1.659] named.
--
--   THE BRIEF'S OBLIGATION  level-laws :
--     Σ[ lf ∈ Formula Code 2 ] (Sound lf × Complete lf)
--   with Sound and Complete verbatim from
--   agents/tasks/LJ-1-659/Probe659.agda:155-161, at [LJ-1.651]'s
--   slot order (ordinal 0, value 1).
--
--   THE OBLIGATION IS NOT INHABITED.  Section 2 splits Complete into
--   a membership that IS built and a satisfaction that is not.
--   Section 3 names the two residues.  The stop is
--   review-of-level-laws.md.
--
--   Nothing is postulated.  No hole.  Nothing lands in src/.
--   ONE Agda process, caliber from the pane, never set here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-663.Probe663 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; ⊤̇ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; Lset; 𝒟ₒ; 𝒟ₒ-intro; Lset-mono )
open import L.BoundedSubset {ℓ} lem using ( module HullStage )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Axioms.Basic {ℓ} using ( Lset-suc )
open import L.Rank {ℓ} using ( rank; rank-fix )
open import L.Ordinal.Stages {ℓ} lem using ( rank-Lset )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; module InfinitySet )
open import Cubical.Data.Sigma using ( _×_ )
open import Cubical.Data.Vec using ( Vec; _∷_; [] )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )
open InfinitySet {ℓ} using ( sucV )

import LJ-1-651.Probe651
module P651 = LJ-1-651.Probe651 {ℓ} lem

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
module SV = hPropStructure 𝒮ᵥ
open SV using ( _∈ˢ_ )

module Level663 (lam : SV.S) (ordλ : IsOrd lam)
                (succλ : (d : SV.S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
                (X : SV.S)
                (X⊆Lλ : (z : SV.S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
                (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  module HS = HullStage lam ordλ succλ X X⊆Lλ ∅∈λ
  module T = HS.H.T
  open T using ( Code; val; _⊨c_ )

  SL : Type (ℓ-suc ℓ)
  SL = HS.ASt.SL

  module P = P651.HullStage lam ordλ succλ X X⊆Lλ ∅∈λ

  -- ===================================================================
  -- SECTION 1.  THE TWO LAWS, VERBATIM FROM THE PREDECESSOR THAT
  --             TYPECHECKED THEM.
  -- ===================================================================

  -- agents/tasks/LJ-1-651/Probe651.agda:141-142.  Verdict GO
  -- (agents/tasks/LJ-1-651/lj-1.651-report.md:3).
  delivered : Formula Code 2
  delivered = P.lset-formula

  -- agents/tasks/LJ-1-659/Probe659.agda:155-161, copied byte for byte
  -- at [LJ-1.651]'s own slot order: ORDINAL 0, VALUE 1, env (γ ∷ v ∷ []).
  Sound : Formula Code 2 → Type (ℓ-suc ℓ)
  Sound lf = (γ v : SL) → ⟨ (γ ∷ v ∷ []) ⊨c lf ⟩ → fst v ≡ Lset (fst γ)

  Complete : Formula Code 2 → Type (ℓ-suc ℓ)
  Complete lf = (γ : SL) → IsOrd (fst γ)
              → ∥ Σ[ v ∈ SL ]
                   ((fst v ≡ Lset (fst γ)) × ⟨ (γ ∷ v ∷ []) ⊨c lf ⟩) ∥₁

  -- THE BRIEF'S OBLIGATION, AS A TYPE.  No term of this type is written
  -- in this file.
  LevelLaws : Type (ℓ-suc ℓ)
  LevelLaws = Σ[ lf ∈ Formula Code 2 ] (Sound lf × Complete lf)

  -- ===================================================================
  -- SECTION 2.  COMPLETE SPLITS, AND THE MEMBERSHIP HALF IS FREE.
  --
  --   Complete asks for a v in the STAGE equal to Lset(γ), and for the
  --   formula to hold of (γ, v).  The first conjunct is a membership
  --   in Lset lam.  It does not mention the formula.  It is built
  --   below from delivered lemmas: rank-fix, rank-Lset, succλ,
  --   𝒟ₒ-intro at ⊤̇ (the EnvSupply spelling,
  --   src/L/Coding/EnvSupply.lagda.md:127-129), Lset-suc, Lset-mono.
  -- ===================================================================

  -- An ordinal of the stage is a member of the index.
  -- rank-fix (src/L/Rank.lagda.md:191) and rank-Lset
  -- (src/L/Ordinal/Stages.lagda.md:190).
  index-of : (γ : SL) → IsOrd (fst γ) → ⟨ fst γ ∈ˢ lam ⟩
  index-of γ oγ =
    subst (λ r → ⟨ r ∈ˢ lam ⟩) (rank-fix (fst γ) oγ)
      (rank-Lset lam ordλ (fst γ) (snd γ))

  -- Lset γ is a member of Lset (suc γ), by the EnvSupply spelling:
  -- 𝒟ₒ-intro at ⊤̇, then Lset-suc.
  Lset∈suc : (γ : SV.S) → IsOrd γ → ⟨ Lset γ ∈ˢ Lset (sucV γ) ⟩
  Lset∈suc γ oγ =
    subst (λ w → ⟨ Lset γ ∈ˢ w ⟩) (sym (Lset-suc γ))
      (𝒟ₒ-intro (Lset γ) (Lset γ) ∣ ⊤̇ , DefA.defSet⊤≡A ∣₁)
    where
    module DefA = DefOf (Lset γ)

  -- THE MEMBERSHIP HALF OF COMPLETE.  Lset(γ) is a member of the stage.
  value-in-stage : (γ : SL) → IsOrd (fst γ) → ⟨ Lset (fst γ) ∈ˢ Lset lam ⟩
  value-in-stage γ oγ =
    Lset-mono {α = lam} {β = sucV (fst γ)}
      (succλ (fst γ) (index-of γ oγ))
      {x = Lset (fst γ)}
      (Lset∈suc (fst γ) oγ)

  -- Pack Lset(γ) as a stage element.
  packed : (γ : SL) (oγ : IsOrd (fst γ)) → SL
  packed γ oγ = Lset (fst γ) , value-in-stage γ oγ

  packed-fst : (γ : SL) (oγ : IsOrd (fst γ))
             → fst (packed γ oγ) ≡ Lset (fst γ)
  packed-fst γ oγ = refl

  -- Satisfaction of lf at the packed pair.  This is the SECOND half of
  -- Complete, and it is the half this file does not inhabit.
  SatAtPacked : Formula Code 2 → Type (ℓ-suc ℓ)
  SatAtPacked lf =
    (γ : SL) (oγ : IsOrd (fst γ))
    → ⟨ (γ ∷ packed γ oγ ∷ []) ⊨c lf ⟩

  -- THE SPLIT.  Complete of lf is exactly SatAtPacked lf, given the
  -- membership half above.  So the truncated existence the brief named
  -- as W3 is not a search for v: v is packed γ oγ.  The truncation is
  -- over the SATISFACTION.
  complete-from-sat : (lf : Formula Code 2) → SatAtPacked lf → Complete lf
  complete-from-sat lf sat γ oγ =
    ∣ packed γ oγ , (packed-fst γ oγ , sat γ oγ) ∣₁

  -- ===================================================================
  -- SECTION 3.  THE TWO RESIDUES, AS TYPES.  No term of either.
  --
  --   Sound of the class-carrier graph is delivered
  --   (src/L/Hierarchy.lagda.md:334-335).  Sound of a Formula Code 2 at
  --   _⊨c_ is not.  The gap is the decode of the bounded matrix, named
  --   HierInK by [LJ-1.532]
  --   (agents/tasks/LJ-1-532/lj-1.532-report.md:171).
  --
  --   Complete of the class-carrier graph is delivered
  --   (src/L/Hierarchy.lagda.md:646-648).  Complete at _⊨c_ reduces to
  --   SatAtPacked (complete-from-sat).  SatAtPacked at the graph needs
  --   the approximation inside the stage: Devlin 2.6(ii), hier-in-stage
  --   of [LJ-1.494]
  --   (agents/tasks/LJ-1-494/review-of-GraphSatAtStage.md:47-53).
  -- ===================================================================

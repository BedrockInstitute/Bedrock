{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.679] PROBE.  Completeness / BoundInStage at [LJ-1.667]'s
-- matrix₃, with SameAsGraph a HYPOTHESIS and IsOrd on the
-- parameter.  Lands nothing in src/.
--
--   W3              the bound's membership in Lset lam.
--                   kvalue-escapes: the tree's KFacts value is the
--                   stage, not a member of it.  tags-in-stage: the
--                   twelve numerals ARE members.  Both in runs/W3.agda.
--   THE OBLIGATION  bound-in-stage.  Not lifted until Completeness
--                   at matrix₃ inhabits, given SameAsGraph.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M2g", the wide
-- caliber, set on the pane by the program and untouched here.
-- Nothing is postulated.  No hole.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-679.Probe679 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; IsOrd; Lset )
open import L.Hierarchy {ℓ} lem using ( hierL )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; module InfinitySet )
open InfinitySet {ℓ} using ( sucV )
open import LJ-1-652.Probe652 {ℓ} lem as P652
import LJ-1-673.Probe673 {ℓ} lem as P673
import LJ-1-520.Probe520 {ℓ} lem as P520
import LJ-1-679.runs.W3 {ℓ} lem as W3

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
module CS = hPropStructure 𝒮ʟ

-- =====================================================================
-- THE PREDECESSOR TYPES, TAKEN NOT REBUILT.  W2.
-- =====================================================================

-- Probe520.agda:192-195.  Both directions.  Class carrier 𝒮ʟ.
SameAsGraph : {n : ℕ} (w b : Fin n) (γ : _) → Type (ℓ-suc ℓ)
SameAsGraph = P520.SameAsGraph

SameHyp : Type (ℓ-suc ℓ)
SameHyp = {n : ℕ} (w b : Fin n) (γ : _) → SameAsGraph w b γ

-- W3, GREEN in runs/W3.agda.  The KFacts supply escapes the stage.
kvalue-escapes = W3.kvalue-escapes
module Tags = W3.Tags

-- =====================================================================
-- COMPLETENESS AT matrix₃, WITH IsOrd ON THE PARAMETER.
-- BoundInStage is Probe673.agda:93-95, not copied.
-- Completeness at Probe673.agda:126-130 has no IsOrd; this restates
-- it with the critic's repair (review-of-LJ-1-673-1.md:157-160).
-- SameAsGraph is a hypothesis of the unwritten term, not of this type.
-- =====================================================================

module At (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : S) (X⊆Lλ : (z : S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩)
  (elem : P652.Frame652.A.Elementary lam ordλ succλ X X⊆Lλ ∅∈λ) where

  module A = P673.At lam ordλ succλ X X⊆Lλ ∅∈λ elem
  open A public using ( BoundInStage; bound-from-stage; inBound )
  open A.F.HS.H.T public using ( Code; val )

  Completeness : Type (ℓ-suc ℓ)
  Completeness =
    (ca cp : Code)
    → IsOrd (fst (val cp))
    → fst (val ca) ≡ Lset (fst (val cp))
    → BoundInStage ca cp

  -- THE REMAINING SUPPLIER.  Re-measured at this stage, not transferred
  -- from [LJ-1.494].  hierL is the witness Lset-defines spends
  -- (src/L/Hierarchy.lagda.md:656).  BoundInStage's ∃̇ ranges over SL
  -- (src/FOL/Semantics.lagda.md:100).  Named, not inhabited.
  HierInStage : Type (ℓ-suc ℓ)
  HierInStage =
    (δ : CS.S) (oδ : IsOrd (fst δ))
    → ⟨ fst δ ∈ˢ Lset lam ⟩
    → ⟨ fst (hierL (fst δ) (δ .snd) oδ) ∈ˢ Lset lam ⟩

  -- Completeness given SameAsGraph AND HierInStage.  Named as a
  -- type, not inhabited.  SameAsGraph is the class-carrier agreement
  -- (Probe520.agda:192-195).  HierInStage is the stage membership
  -- the AbsL existential spends.  Either unpaid stops bound-in-stage.
  CompletenessFrom : Type (ℓ-suc ℓ)
  CompletenessFrom = SameHyp → HierInStage → Completeness

-- CompletenessFrom is a named supplier, not the obligation.  The
-- obligation name bound-in-stage is NOT defined.  The witness meter
-- must read UNRESOLVED.  See review-of-bound-in-stage.md.

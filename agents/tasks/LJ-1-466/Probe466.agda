{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.466] PROBE.  The hull codes for the constants of LsetGraph.
-- It runs in agents/tasks/LJ-1-466/ and lands nothing in src/.
--
--   STEP ONE, W3 FIRST  how-many = countFo LsetGraph.
--                       Forced against zero: UnequalTerms, suc
--                       against zero.  Not a closed literal.
--                       See runs/w3-force.out.
--
--   STEP TWO            D-10 census.  constantsFo is Vec CS.S.
--                       base wants ⟪ X ⟫.  No term named
--                       lset-codes.  See review-of-lset-codes.md.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-466.Probe466 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import FOL.Manipulation.Parameters using ( absFo; countFo; constantsFo )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; Lset; 𝒮ʟ )
open import L.Hull {ℓ} lem using ( module AtStage )
open import L.Coding.Sequence {ℓ} lem using ( LsetGraph )
open import V.Collapse {ℓ} using ( module Collapse )

open import Cubical.Data.Nat using ( ℕ; _+_ )
open import Cubical.Data.Vec using ( Vec; _∷_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; module InfinitySet )
open InfinitySet using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
module CS = hPropStructure 𝒮ʟ

-- =====================================================================
-- W3.  The length of the missing vector.
-- =====================================================================

how-many : ℕ
how-many = countFo LsetGraph

-- Same packaging [LJ-1.462] delivered.  Probe462.agda:66-67.
packaged : Formula (⊥* {ℓ}) (2 + countFo LsetGraph)
packaged = absFo {ℓz = ℓ} LsetGraph

-- The formula's own constants, at the class carrier.  Not Code.
consts : Vec CS.S (countFo LsetGraph)
consts = constantsFo LsetGraph

-- Telescope copied from src/L/BoundedSubset.lagda.md:903-914.
-- Nothing below module Condense is copied.

module HullStage (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : S) (X⊆L : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  module ASt = AtStage lam ordλ

  module H = ASt.Hull X X⊆L ∅∈λ

  M : S
  M = H.T.Hull

  module C = Collapse M

  -- Code constructors in scope: base and wit.  There is no third.
  -- base : ⟪ X ⟫ → Code   at src/L/Hull.lagda.md:73,323
  open H.T using ( Code; val; base; wit )

  -- [LJ-1.462] feed, Probe462.agda:101-102.  The extra Vec is the
  -- obligation.  It is not delivered: consts is Vec CS.S, not Vec Code.
  feed : (c : Code) (cs : Vec Code (countFo LsetGraph)) → Code
  feed c cs = wit (suc (countFo LsetGraph)) packaged (c ∷ cs)

  -- No term named lset-codes.  Mapping base over consts does not
  -- typecheck: base takes ⟪ X ⟫ and consts holds class-carrier
  -- numerals.  The condition on X is in the report.

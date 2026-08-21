{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.477] PROBE.  Does the collapse commute with the stage
-- operation.  Lands nothing in src/.
--
--   STEP ONE, W3 FIRST  both-compute: apply π-compute at Lset y.
--                       Obligation omitted.  π is opaque.  Its law
--                       sits inside an unfolding block at
--                       src/V/Collapse.lagda.md:56-59.  This file
--                       spends the exported law and does not open
--                       the seal.
--
--   STEP TWO            Both computation laws spent.  The join of
--                       their right-hand sides is the remaining type.
--                       No term named piCommuteLset.  See
--                       review-of-piCommuteLset.md.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-477.Probe477 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; Lset; LsetStep; Lset-compute )
open import L.Hull {ℓ} lem using ( module AtStage )
open import V.Collapse {ℓ} using ( module Collapse )

open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; module InfinitySet )
open InfinitySet using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- Telescope copied from src/L/BoundedSubset.lagda.md:903-916.
-- Line :903 is the module keyword.  Line :916 is `module Condense`.
-- Nothing below that header is copied.  Same cut as
-- Probe462.agda:78-90.

module HullStage (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : S) (X⊆L : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  module ASt = AtStage lam ordλ

  module H = ASt.Hull X X⊆L ∅∈λ

  M : S
  M = H.T.Hull

  module C = Collapse M

  -- =====================================================================
  -- W3.  Spend π-compute at Lset y.  Obligation omitted.
  -- =====================================================================

  -- π-compute : (x : S) → π x ≡ step x (λ y _ → π y)
  -- Site: src/V/Collapse.lagda.md:58-59, inside `opaque; unfolding π`.
  -- The type is visible without unfolding.  This term applies the
  -- exported law at Lset y and does not open the seal on π.

  both-compute : (y : S) → C.π (Lset y) ≡ _
  both-compute y = C.π-compute (Lset y)

  -- =====================================================================
  -- STEP TWO.  The other computation law at the same argument, then
  -- the join.  No term named piCommuteLset.
  -- =====================================================================

  -- Lset-compute : (α : S) → Lset α ≡ LsetStep α (λ β _ → Lset β)
  -- Site: src/L/Constructible.lagda.md:227-228, inside
  -- `opaque; unfolding Lset`.  Spent at C.π y.  The type is visible
  -- without unfolding.  This term does not open the seal on Lset.

  after-L : (y : S) → Lset (C.π y) ≡ _
  after-L y = Lset-compute (C.π y)

  -- The join the two laws leave.  Left is C.step at Lset y, a sett of
  -- π-images of hull-filtered members of Lset y
  -- (src/V/Collapse.lagda.md:47-48).  Right is LsetStep at C.π y, a
  -- union of 𝒟ₒ of Lset at members of C.π y
  -- (src/L/Constructible.lagda.md:215-216).  UNBUILT.

  JoinSteps : Type (ℓ-suc ℓ)
  JoinSteps =
    (y : S) → C.step (Lset y) (λ z _ → C.π z)
            ≡ LsetStep (C.π y) (λ β _ → Lset β)

  -- Predecessor type, Probe462.agda:140-142.  Same type, unbuilt.
  -- The obligation name is piCommuteLset.  That name is not in
  -- scope.  HullClosedLset is not taken as a module hypothesis:
  -- the type does not mention ⟨ Lset y ∈ˢ M ⟩.

  PiCommuteLset : Type (ℓ-suc ℓ)
  PiCommuteLset =
    (y : S) → ⟨ y ∈ˢ M ⟩ → C.π (Lset y) ≡ Lset (C.π y)

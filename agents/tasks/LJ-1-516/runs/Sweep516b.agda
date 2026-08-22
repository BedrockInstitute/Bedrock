{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.516] C-42 SWEEP, second pass.  The sites the first pass could not
-- settle by inspection.  Kept apart from Sweep516.agda so one failing line
-- does not hide the others.
--
-- satGraphAt is sealed (src/L/Coding/Graph.lagda.md:203), so its Δ₀
-- question is stuck behind the seal until the seal is opened here.  That
-- is [LJ-1.514]'s finding reused: opening it is reading and not editing.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-516.runs.Sweep516b {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.LevyHierarchy using ( Δ₀; δ-∧; δ-∀∈ )
open import L.Coding.Graph {ℓ} lem using ( satGraphAt )

-- NOT REFUTABLE, and each is bounded BY CONSTRUCTION.  Kept as comments
-- with the run that measured them, in [LJ-1.514]'s protocol.
--
--   closedAt  (src/L/Coding/Model.lagda.md:2191).  Its first conjunct
--   andClosedAt is δ-∀∈ and Agda named the constructor itself:
--   runs/sweep-2.out:3-6, the [ShouldBeEmpty] report on
--   `Δ₀ (L.Coding.Model.andClosedAt w)`.
--   -- s15 : Δ₀ (closedAt w) → ⊥* {ℓ}
--   -- s15 (δ-∧ () _)
--
--   shapedAt (src/L/Coding/Shape.lagda.md:189) is ∀̇∈ (var C) (shapes A),
--   so δ-∀∈ applies to it by inspection and no run is spent on it.
--
--   appAt (src/L/Coding/Model.lagda.md:160) and prAtL (:122) are GRADED
--   in the tree already: Δ₀-appAtK (src/L/Coding/Key.lagda.md:187) and
--   Δ₀-prAtLK (:184).  Refuting them would refute delivered theorems.

module _ {n : ℕ} (w b : Fin n) where

  opaque
    unfolding satGraphAt
    s09 : Δ₀ (satGraphAt w b w) → ⊥* {ℓ}   -- Graph:204
    s09 ()

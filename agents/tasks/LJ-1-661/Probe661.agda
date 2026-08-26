{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.661] PROBE.  Pin the level-hood formula and read `Lset` off it.
-- The brief's obligation, `hoodsound-at-levelhood0`, is [LJ-1.658]'s
-- `soundP-leg2-from-pix` instantiated at a PINNED `φ₀` with `Δ₀ φ₀` and
-- `LsetOnlyAt φ₀` both supplied (agents/tasks/LJ-1-658/Probe658.agda:
-- 317-325).  Lands nothing in src/.
--
-- THE VERDICT IS NO-GO, stated in review-of-hoodsound-at-levelhood0.md.
-- Two sites were checked, and each fails at a different input:
--
--   SITE A   The only pin the delivered supplier `Lset-only`
--            (src/L/Hierarchy.lagda.md:334-335) covers is `LsetGraph`
--            (src/L/Coding/Sequence.lagda.md:353-354).  Its leading
--            constructor is the unbounded `∃̇`
--            (src/L/Coding/Sequence.lagda.md:291-292), and `data Δ₀`
--            has no case for it (src/FOL/LevyHierarchy.lagda.md:47-57).
--            Moreover the pin term itself cannot be stated in the tree:
--            its erasure needs `countFo LsetGraph ≡ 0`, and the count
--            does not compute, because the core `satGraphAt` is opaque
--            (src/L/Coding/Graph.lagda.md:203-205).  Both holes live in
--            Wall661.agda.txt; the count failure is measured in
--            runs/floor-1.out.
--
--   SITE B   The chapter's own shape.  The Δ₀ certificate the chapter
--            has is the arity-4 matrix with the bound `K` free
--            (src/L/BoundedSubset.lagda.md:847-852), and its unbounded
--            projection is Σ₁ by the chapter's own certificate
--            (src/L/BoundedSubset.lagda.md:855-859).  PART 2 states
--            both, green, and adds the arity-3 and arity-2 readings of
--            the matrix at the supplier's slot convention.
--
--   THERE IS NO ARITY-2 Δ₀ PIN.  The obligation's name is therefore NOT
--   stated in this file: a qualified reference to an absent name is the
--   witness meter's [NotInScope], and that reading is the NO-GO.
--
-- ONE Agda process per run, GHCRTS wide caliber, set on the pane by the
-- program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-661.Probe661 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; ∃̇_ )
open import FOL.LevyHierarchy using ( Δ₀; Σ₁; σ-Δ₀; σ-∃ )
open import FOL.Manipulation.Parameters using ( countFo )
open import FOL.Manipulation.Renaming using ( renameFo )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.Coding.Sequence {ℓ} lem using ( LsetGraph )
open import L.BoundedSubset {ℓ} lem using ( module LevelHood0 )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))

-- the class carrier, the constant domain of the chapter's formulas
-- (src/L/BoundedSubset.lagda.md:61)
module CS = hPropStructure 𝒮ʟ

-- =====================================================================
-- PART 1.  SITE A:  THE SUPPLIER'S PIN.
-- =====================================================================

-- The arity-2 formula the supplier speaks of (imported, stated here
-- for the record): it is the unbounded twin of the chapter's bounded
-- matrix, at the class carrier, env (value ∷ ordinal).
--
-- Its leading constructor is definitionally visible: `GraphAt` is
-- transparent (src/L/Coding/Sequence.lagda.md:291-292),
--
--   GraphAt w b = ∃̇ (ApproxAt zero (suc b) ∧̇ Step (suc w) (suc b) zero)
--
-- and runs/floor-1.out shows the count recursion unfolding `LsetGraph`
-- to the count of exactly that body.  The Δ₀ input of the obligation at
-- this pin is empty: `data Δ₀` has one constructor per allowed shape and
-- no case for `∃̇` (src/FOL/LevyHierarchy.lagda.md:47-57), and erasure
-- would preserve the shape (src/FOL/Count.lagda.md:607).
--
-- The pin term itself cannot be stated: its erasure
-- `Cnt.erase LsetGraph p` needs `p : countFo LsetGraph ≡ 0`, and the
-- count is stuck on the opaque core `satGraphAt`
-- (src/L/Coding/Graph.lagda.md:203-205; the official unfoldings are the
-- readers, not a rewrite, src/L/Coding/Graph.lagda.md:207-216).  The
-- failure is measured: runs/floor-1.out, `refl` at the count.  Both
-- holes are in Wall661.agda.txt.
--
-- The campaign has measured the grade of this formula before:
-- [LJ-1.646] counted 2,287 unbounded `∃̇` and 2,159 unbounded `∀̇` in its
-- expansion (agents/tasks/LJ-1-646/lj-1.646-report.md:82).

-- =====================================================================
-- PART 2.  SITE B:  THE CHAPTER'S OWN SHAPE.
-- =====================================================================

-- The chapter's instantiation at n = 0, all Fin slots zero, the
-- delivered convention (agents/tasks/LJ-1-651/Probe651.agda:73-77).
module LH0 = LevelHood0
  zero zero zero zero zero zero zero zero zero zero zero zero zero zero
  zero zero zero zero zero zero zero zero zero zero zero zero zero zero

-- The only Δ₀ certificate the chapter has for the level-hood statement:
-- the bounded matrix, arity 4, env u ∷ v ∷ γ ∷ K, K the one free bound
-- (src/L/BoundedSubset.lagda.md:847-852).  Arity 4: not the hole's 2.
Δ₀-matrix : Δ₀ LH0.matrix
Δ₀-matrix = LH0.Δ₀-matrix

-- The chapter's unbounded projection is Σ₁, certified by the chapter
-- itself (src/L/BoundedSubset.lagda.md:855-859).  Grade Σ₁: not Δ₀.
Σ₁-Σ₂ : Σ₁ LH0.Σ₂
Σ₁-Σ₂ = LH0.Σ₁-Σ₂

-- The matrix is a normal form: its erasure count is `refl`
-- (re-measured here; first measured at agents/tasks/LJ-1-651/
-- Probe651.agda:73-74).
count-matrix : countFo LH0.matrix ≡ 0
count-matrix = refl

-- The arity-3 reading at the supplier's slot convention, value slot 0,
-- ordinal slot 1, bound slot 2, closing the unused u slot:
-- one unbounded `∃̇` over the Δ₀ matrix, so Σ₁, graded.
step1 : Formula CS.S 3
step1 = ∃̇ LH0.matrix

Σ₁-step1 : Σ₁ step1
Σ₁-step1 = σ-∃ (σ-Δ₀ Δ₀-matrix)

-- The arity-2 reading at the supplier's slot convention, value slot 0,
-- ordinal slot 1, closing the bound K: the shape of the obligation's
-- hole, built from the chapter's matrix.  Its grade is Σ₁, two
-- unbounded closures over the Δ₀ core.  The tree has no
-- rename-preservation lemma for `Σ₁`, so the certificate is stated in
-- the review rather than built here.
rot : Fin 3 → Fin 3
rot zero           = suc zero
rot (suc zero)     = suc (suc zero)
rot (suc (suc zero)) = zero

step2 : Formula CS.S 3
step2 = renameFo rot step1

step3 : Formula CS.S 2
step3 = ∃̇ step2

-- =====================================================================
-- PART 3.  THE ABSENCE.
-- =====================================================================
--
-- The obligation's hole is one pin `φ₀ : Formula (⊥* {ℓ-suc ℓ}) 2` with
-- both `Δ₀ φ₀` and `LsetOnlyAt φ₀` supplied.  Site A covers the
-- supplier and fails the Δ₀ input at the leading `∃̇`, and the pin term
-- is unstateable there (measured).  Site B covers the Δ₀ core and fails
-- the hole's arity and the supplier: its certificate is at arity 4 with
-- a free bound, its readings at arity 3 and 2 are Σ₁, and `Lset-only`
-- speaks of `LsetGraphAt w b` (src/L/Coding/Sequence.lagda.md:291-292),
-- not of the chapter's matrix.  No pin has both inputs.  See
-- review-of-hoodsound-at-levelhood0.md.

{-# OPTIONS --cubical --safe --guardedness -WnoUselessOpaque #-}

-- [LJ-1.714] PROBE.  binder-count, the exact count of relativized
-- binders in the relativized pair-graph [LJ-1.698] built.  Lands
-- nothing in src/.
--
--   THE OBLIGATION  binder-count.  MEASURED below; the numeral in its
--                   type is refused by the typechecker unless it is
--                   exactly what the syntax computes.
--   METHOD          unb counts unbounded quantifier nodes of the
--                   object syntax.  relativize
--                   (src/FOL/Manipulation/Relativize.lagda.md:57-58)
--                   turns each unbounded quantifier into exactly one
--                   binder whose bound is the relativizer constant,
--                   and changes nothing else, so the source-side count
--                   IS the count of relativized binders carried by the
--                   relativized formula.  conb counts constant-bound
--                   binders, which pins the same number on the
--                   relativized formula itself: its constant-bound
--                   binders are the N relativized ones plus the one
--                   passed-through outer bound at con γ
--                   (src/FOL/Manipulation/Relativize.lagda.md:60).
--   Delivered       unb, conb (generic in the constant domain),
--                   recordedFo verbatim Probe698.agda:84-85,
--                   binder-count, conb-rel, rel-unb.  No postulate,
--                   no hole.
--
-- ONE Agda process per run, GHCRTS wide caliber, set on the pane by
-- the program and untouched here.

open import Base.Prelude
open import Base.Classical using ( LEM )

module LJ-1-714.Probe714 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.Syntax
  using ( Formula; con; var; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊤̇; ⊥̇
        ; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import FOL.Manipulation.Relativize using ( relativize )
open import FOL.ZFStructure using ( module hPropStructure )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.Coding.Sequence {ℓ} lem using ( PairGraphAt )
open import L.Coding.Graph {ℓ} lem using ( satGraphAt )
open import Cubical.Data.Nat using ( ℕ; _+_; zero; suc )
open import Cubical.Data.FinData renaming ( zero to fzero; suc to fsuc )

open hPropStructure 𝒮ʟ using ( S )


-- =====================================================================
-- SECTION 1.  THE TWO COUNTERS.  Generic in the constant domain: the
-- counters read only the SHAPE of the syntax, never a constant's
-- payload, so the counts below cannot depend on γ or on the
-- relativizer.  unb counts the unbounded quantifier nodes; conb counts
-- the bounded quantifier nodes whose bound is a constant.
-- =====================================================================

unb : ∀ {k} {K : Type k} {n} → Formula K n → ℕ
unb (t ∈̇ u)  = zero
unb (t ≐ u)  = zero
unb (φ ∧̇ ψ)  = unb φ + unb ψ
unb (φ ∨̇ ψ)  = unb φ + unb ψ
unb (φ ⇒̇ ψ)  = unb φ + unb ψ
unb (¬̇ φ)    = unb φ
unb ⊤̇        = zero
unb ⊥̇        = zero
unb (∃̇ φ)    = suc (unb φ)
unb (∀̇ φ)    = suc (unb φ)
unb (∀̇∈ t φ) = unb φ
unb (∃̇∈ t φ) = unb φ

conb : ∀ {k} {K : Type k} {n} → Formula K n → ℕ
conb (t ∈̇ u)  = zero
conb (t ≐ u)  = zero
conb (φ ∧̇ ψ)  = conb φ + conb ψ
conb (φ ∨̇ ψ)  = conb φ + conb ψ
conb (φ ⇒̇ ψ)  = conb φ + conb ψ
conb (¬̇ φ)    = conb φ
conb ⊤̇        = zero
conb ⊥̇        = zero
conb (∃̇ φ)    = conb φ
conb (∀̇ φ)    = conb φ
conb (∃̇∈ (con c) φ) = suc (conb φ)
conb (∀̇∈ (con c) φ) = suc (conb φ)
conb (∃̇∈ (var i) φ) = conb φ
conb (∀̇∈ (var i) φ) = conb φ


-- =====================================================================
-- SECTION 2.  THE FORMULA.  Verbatim Probe698.agda:87-88: the recorded
-- pair-graph, bound by the outer con γ.  relativize A of it is the
-- relativized pair-graph that mkBoundedFo bounds (Probe698.agda:97-101).
-- =====================================================================

recordedFo : S → Formula S 1
recordedFo γ = ∃̇∈ (con γ) (PairGraphAt (fsuc fzero) fzero)


-- =====================================================================
-- SECTION 3.  THE OBLIGATION.  Three rows, each an equality the
-- typechecker refuses if the numeral is not what the syntax computes.
-- The counts are stated at a GENERIC γ and a GENERIC relativizer A:
-- Section 1's counters never look at a constant's payload, so the
-- count is independent of both.  Instantiating A := LsetS γ oγ gives
-- the [LJ-1.698] instance unchanged.
--
-- The rows sit inside the unfolding block, because that is what the
-- block is FOR: the equality is refused by REDUCING the counter over
-- the formula, and the counter must see every quantifier node.
-- satGraphAt (L.Coding.Graph.lagda.md:204-205) is sealed under
-- `opaque` by a measured seal (the comment there names the 2,459 ms
-- coercion it prevents; its two readers are the official unfolding
-- for WITNESSES, not for shape).  Here the formula's SHAPE is what is
-- read, so the seal is lifted for exactly the rows below, on this
-- file's own authority.  Same pattern as
-- src/L/Condensation.lagda.md:7186-7187, the tree's one other
-- consumer-side opening.  With the seal on, unb is STUCK at
-- satGraphAt and the count does not reduce (runs/run-4.out); with it
-- lifted, the counter runs to the end and the mismatch, if any, is
-- numeral against numeral.
opaque
  unfolding satGraphAt

  -- THE OBLIGATION.  The exact count of relativized binders the
  -- relativized pair-graph carries: every unbounded quantifier of
  -- recordedFo γ becomes exactly one binder at con A
  -- (Relativize.lagda.md:57-58), and nothing else gains or loses one.
  binder-count : (γ : S) → unb (recordedFo γ) ≡ 4447
  binder-count γ = refl

  -- The same count, pinned on the relativized formula itself.  Its
  -- constant-bound binders are the N relativized ones plus the one
  -- passed-through outer bound at con γ (Relativize.lagda.md:60), so
  -- the refusal point is N + 1.
  conb-rel : (γ A : S) → conb (relativize A (recordedFo γ)) ≡ 4448
  conb-rel γ A = refl

  -- The relativized formula has no unbounded quantifier left
  -- (Relativize.lagda.md:64-66).
  rel-unb : (γ A : S) → unb (relativize A (recordedFo γ)) ≡ zero
  rel-unb γ A = refl

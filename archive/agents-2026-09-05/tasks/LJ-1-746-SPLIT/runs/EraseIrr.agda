{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.746] runs/EraseIrr.  THE RESTRUCTURE LEMMA the heap wall
-- demanded.  erase recurses on its count proof
-- (src/FOL/Count.lagda.md:598-610: every clause hands the split
-- proofs plus-zero-l / plus-zero-r down), so two spellings of the
-- same zero-count proof are not definitionally equal terms, and a
-- consumer comparing a named row against an erase-split of a bigger
-- erased formula normalizes countFo over the whole unfolded tree.
-- MEASURED THIS TASK at the Amb4 site: a bare refl between the two
-- spellings ground past 120 s (runs/b7-3.out), and the full component
-- check died at 342.78 s with heap exhausted at the 2 g wide caliber
-- cap (runs/amb4-746-3.out, peak RSS 2.4 GB).
--
-- THE CURE is this file: erase-cong transports at the FORMULA level
-- in O(|φ|) cong steps, so no consumer normalizes the semantics.  It
-- is the machine form of the claim Amb2's 732 comment made at
-- prose level: the erase result does not depend on which zero-count
-- proof is passed down.  The tree's BoundedSubset.erase-Δ₀
-- (src/L/BoundedSubset.lagda.md:825-837) transports Delta-0 through
-- ONE proof; nothing in the tree carried BOTH proofs, so this module
-- writes it, outside src/ (the brief lands nothing there).
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M2g", the wide
-- caliber, set on the pane by the program and untouched here.
-- Nothing is postulated.  No hole in the delivered file.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.Syntax
  using ( Term; Formula; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊤̇; ⊥̇
        ; ∃̇_; ∀̇_; ∃̇∈; ∀̇∈ )
open import FOL.Manipulation.Parameters using ( countTm; countFo )
open import FOL.Count
open import Cubical.Data.Nat using ( snotz )
import Cubical.Data.Empty as Empty

module LJ-1-746-SPLIT.runs.EraseIrr {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

module Irr (K : Type (ℓ-suc ℓ)) where
  private
    module C = FOL.Count.Count {ℓ = ℓ-suc ℓ} K
  open C public

  -- the term-level half: eraseTm keeps vars and dies on constants, so
  -- the two spellings agree by the same case tree.
  eraseTm-cong : {n : ℕ} (t : Term K n) (p q : countTm t ≡ 0)
               → eraseTm t p ≡ eraseTm t q
  eraseTm-cong (con a) p q = Empty.rec (snotz p)
  eraseTm-cong (var i) p q = refl

  -- THE LEMMA.  erase φ p ≡ erase φ q, by induction on φ; every case
  -- is cong-structural and no clause reads the proofs beyond the
  -- same splits erase itself performs.
  erase-cong : {n : ℕ} (φ : Formula K n) (p q : countFo φ ≡ 0)
             → erase φ p ≡ erase φ q
  erase-cong (t ∈̇ u) p q =
    cong₂ _∈̇_ (eraseTm-cong t (plus-zero-l p) (plus-zero-l q))
              (eraseTm-cong u (plus-zero-r p) (plus-zero-r q))
  erase-cong (t ≐ u) p q =
    cong₂ _≐_ (eraseTm-cong t (plus-zero-l p) (plus-zero-l q))
              (eraseTm-cong u (plus-zero-r p) (plus-zero-r q))
  erase-cong (φ ∧̇ ψ) p q =
    cong₂ _∧̇_ (erase-cong φ (plus-zero-l p) (plus-zero-l q))
              (erase-cong ψ (plus-zero-r p) (plus-zero-r q))
  erase-cong (φ ∨̇ ψ) p q =
    cong₂ _∨̇_ (erase-cong φ (plus-zero-l p) (plus-zero-l q))
              (erase-cong ψ (plus-zero-r p) (plus-zero-r q))
  erase-cong (φ ⇒̇ ψ) p q =
    cong₂ _⇒̇_ (erase-cong φ (plus-zero-l p) (plus-zero-l q))
              (erase-cong ψ (plus-zero-r p) (plus-zero-r q))
  erase-cong (¬̇ φ) p q = cong ¬̇_ (erase-cong φ p q)
  erase-cong ⊤̇ p q = refl
  erase-cong ⊥̇ p q = refl
  erase-cong (∃̇ φ) p q = cong ∃̇_ (erase-cong φ p q)
  erase-cong (∀̇ φ) p q = cong ∀̇_ (erase-cong φ p q)
  erase-cong (∃̇∈ t φ) p q =
    cong₂ ∃̇∈ (eraseTm-cong t (plus-zero-l p) (plus-zero-l q))
              (erase-cong φ (plus-zero-r p) (plus-zero-r q))
  erase-cong (∀̇∈ t φ) p q =
    cong₂ ∀̇∈ (eraseTm-cong t (plus-zero-l p) (plus-zero-l q))
              (erase-cong φ (plus-zero-r p) (plus-zero-r q))

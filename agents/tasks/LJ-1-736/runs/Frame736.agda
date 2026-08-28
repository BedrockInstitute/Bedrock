{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.736] FLOOR FRAME for Probe736: imports + stated type, kernel absent, the Sat value bound at the
-- closedomega scope.  Lands nothing in src/.
--
--   OBLIGATION  Sat-in-carrier-lim (the type in Section 2).  STATED,
--               NOT INHABITED.  The D-10 truth check (brief premise 4)
--               prices the target FALSE:  the obligation quantifies
--               over Formula S n, whose constants range over ALL L-sets
--               (FOL.Absoluteness.Single's SM), and the atom clause of
--               `cond` transports a constant's global membership into
--               Sat's extension.  Section 1 machine-checks that
--               transport, so the review does not rest on a reading of
--               tmIs.  review-of-Sat-in-carrier-lim.md carries the
--               statement and the corrected-scope candidates.
--   DELIVERED   the semantic kernel (Section 1):  for the atom
--               (var 0 INdot con c), satisfaction of Sat's own `cond`
--               at an environment x is INTERMEDIATE-EXACTLY the fact
--               that the #0-tagged entry of x lies in c, for EVERY
--               carrier A, environment x and constant c : S, with no
--               stage hypothesis anywhere.  sat-atom-out lifts it to
--               Sat's own membership spec.
--   ABSENT      the INHABITANT of Sat-in-carrier-lim.  No postulate
--               stands in for it and no weaker form is inhabited under
--               its name.  Sat-in-carrier-stage and
--               envSet-in-carrier-stage are not inhabited either.
--
-- ONE Agda process per run, GHCRTS wide caliber, set on the pane by
-- the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-736.runs.Frame736 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _∈̇_ )
import FOL.Absoluteness
open import Cubical.Data.FinData using ( zero; suc )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( #_; ω )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset )
open import L.Ordinal.StageArith {ℓ} lem using ( closedω )
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import L.Coding.Sat {ℓ} lem
  using ( Sat; cond; Sat-mem; tmIs; tmIs-var-in; tmIs-var-out
        ; cond∈-in; cond∈-out )
open import L.Coding.EnvSet {ℓ} lem using ( envSet )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

-- The satisfaction symbol.  THE SAME instance Sat itself opens
-- (src/L/Coding/Sat.lagda.md:57-58):  Single at 𝒮ᵥ with isL, so
-- `_⊨_` below is literally the satisfaction of Sat-mem's clause.
module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using () renaming ( _⊨ᵐ_ to _⊨_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))

-- The brief's hypothesis glyph `omega in^s gamma` reads at the V
-- structure (gamma : V), so it is renamed here;  the conclusion's
-- glyph `Sat A phi in^s LsetS gamma ogamma` is the L structure's and
-- stays unrenamed below.  (The 725-SPLIT disambiguation, as in
-- Probe729 and Probe730.)
open hPropStructure 𝒮ᵥ using () renaming ( _∈ˢ_ to _∈ˢᵥ_ )
open hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )

-- =====================================================================
-- SECTION 2.  THE OBLIGATION'S TYPE.  STATED, NOT INHABITED.
--
-- The brief's type, verbatim up to the two membership glyphs:  the
-- hypothesis reads at the V structure (renamed in Section 0), the
-- conclusion at the L structure.  The name is exported at the file's
-- top level;  no inhabitant stands under it, no postulate supports
-- it, and the file carries --safe.  Section 1 is the machine-checked
-- half of the review's FALSE verdict on this type.
-- =====================================================================

Sat-in-carrier-lim : Type (ℓ-suc ℓ)
Sat-in-carrier-lim =
    (γ : V ℓ) (oγ : IsOrd γ) (clγ : closedω γ)
    (ω∈γ : ⟨ ω ∈ˢᵥ γ ⟩)
    (A : S) (hA : ⟨ fst A ∈ Lset γ ⟩)
    {n : ℕ} (φ : Formula S n)
  → ⟨ Sat A φ ∈ˢ LsetS γ oγ ⟩

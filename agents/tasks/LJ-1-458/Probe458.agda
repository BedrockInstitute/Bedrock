{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.458] PROBE.  The formula the tree already wrote, under another name.
-- It runs in agents/tasks/LJ-1-458/ and lands nothing in src/.
--
--   STEP ONE, W3 FIRST  stage-mentioning : Formula S 2
--                       Inhabited by the delivered LsetGraph.
--                       Typechecked ALONE (runs/w3-{1,2,3,4}).
--
--   STEP TWO            LsetAt = LsetGraphAt (delivered, same type).
--                       lsetAt-out = Lset-only (delivered, extra IsOrd).
--                       The brief's lsetAt-out type omits IsOrd. Unbuilt.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-458.Probe458 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; Lset; IsOrd )
open import L.Coding.Sequence {ℓ} lem using ( LsetGraph; LsetGraphAt )
open import L.Hierarchy {ℓ} lem using ( Lset-only )
open import Cubical.Data.FinData using ( Fin )
open import Cubical.Data.Vec using ( lookup )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- =====================================================================
-- W3.  The type the brief names.  Inhabited from ONE delivered formula
-- whose satisfaction speaks about Lset at a slot: LsetGraph at
-- src/L/Coding/Sequence.lagda.md:353, which is LsetGraphAt zero (suc zero)
-- at :349.  Hierarchy.lagda.md:334-335 (Lset-only) is the adequacy that
-- names Lset.
-- =====================================================================

stage-mentioning : Formula S 2
stage-mentioning = LsetGraph

-- =====================================================================
-- OBLIGATION.  Same type as LsetGraphAt.  Inhabited from the delivered
-- term.  No new formula.  No well-founded recursion inside a formula.
-- =====================================================================

LsetAt : ∀ {n} → Fin n → Fin n → Formula S n
LsetAt = LsetGraphAt

-- Delivered adequacy.  Extra IsOrd.  Site: src/L/Hierarchy.lagda.md:334-335.
-- The brief's type omits IsOrd.  That stronger type is not delivered.
-- I did not inhabit it.  I did not postulate.  See LsetAt-out-brief.

lsetAt-out : ∀ {n} (x d : Fin n) (γ : S ^ n)
           → ⟨ γ ⊨ LsetAt x d ⟩
           → IsOrd (fst (lookup d γ))
           → fst (lookup x γ) ≡ Lset (fst (lookup d γ))
lsetAt-out = Lset-only

-- The brief's adequacy, without IsOrd.  Stated.  Unbuilt.
LsetAt-out-brief : Type _
LsetAt-out-brief =
    ∀ {n} (x d : Fin n) (γ : S ^ n)
  → ⟨ γ ⊨ LsetAt x d ⟩
  → fst (lookup x γ) ≡ Lset (fst (lookup d γ))

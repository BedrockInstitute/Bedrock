{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.462] PROBE.  levelIn again, with the formula the tree has.
-- It runs in agents/tasks/LJ-1-462/ and lands nothing in src/.
--
--   STEP ONE, W3 FIRST  lset-code, obligation omitted.
--                       Feed LsetGraphAt to wit. The two formula
--                       types do not meet. Packaging is absFo, not
--                       subst. Extra Vec Code for the constants.
--                       IsOrd does not arise on Code.
--
--   STEP TWO            D-10 types only. W3 unbuilt. No term
--                       named levelIn. See review-of-levelIn.md.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-462.Probe462 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import FOL.Manipulation.Parameters using ( absFo; countFo )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; Lset; 𝒮ʟ )
open import L.Hull {ℓ} lem using ( module AtStage )
open import L.Coding.Sequence {ℓ} lem using ( LsetGraph; LsetGraphAt )
open import V.Collapse {ℓ} using ( module Collapse )

open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Data.Sigma using ( Σ-syntax )
open import Cubical.Data.Vec using ( Vec; _∷_; [] )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; module InfinitySet )
open InfinitySet using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
module CS = hPropStructure 𝒮ʟ

-- =====================================================================
-- W3.  Meeting of the two formula types.  Obligation omitted.
-- =====================================================================

-- LsetGraphAt : ∀ {n} → Fin n → Fin n → Formula CS.S n
-- Site: src/L/Coding/Sequence.lagda.md:349
-- LsetGraph = LsetGraphAt zero (suc zero)  at :353-354
--
-- wit : (k : ℕ) → Formula (⊥* {ℓ}) (suc k) → Vec Code k → Code
-- Site: src/L/Hull.lagda.md:74
--
-- They do not meet. Formula CS.S 2 lives in Type (ℓ-suc ℓ).
-- Formula (⊥* {ℓ}) 2 lives in Type ℓ. A subst cannot join them.
--
-- Packaging, not a subst: absFo at
-- src/FOL/Manipulation/Parameters.lagda.md:260.

graph : Formula CS.S 2
graph = LsetGraph

packaged : Formula (⊥* {ℓ}) (2 + countFo LsetGraph)
packaged = absFo {ℓz = ℓ} LsetGraph

-- Same term as graph. LsetGraph is LsetGraphAt zero (suc zero)
-- at src/L/Coding/Sequence.lagda.md:353-354.
graphAt : Formula CS.S 2
graphAt = LsetGraphAt {n = 2} zero (suc zero)

-- Telescope copied from src/L/BoundedSubset.lagda.md:903-914.
-- The brief names :898-916 (comment plus Condense header). Nothing
-- below module Condense is copied.

module HullStage (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : S) (X⊆L : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  module ASt = AtStage lam ordλ

  module H = ASt.Hull X X⊆L ∅∈λ

  M : S
  M = H.T.Hull

  module C = Collapse M

  -- Code constructors in scope: base and wit. There is no third.
  open H.T using ( Code; val; base; wit )

  -- Feeding the packaged graph to wit. The extra Vec Code holds
  -- codes for the class-carrier constants of LsetGraphAt
  -- (tagAtL names con (numeralL k) at src/L/Coding/Model.lagda.md:586).
  -- Those codes are not delivered: constantsFo LsetGraph is Vec CS.S,
  -- not Vec Code. This term is not lset-code.

  feed : (c : Code) (cs : Vec Code (countFo LsetGraph)) → Code
  feed c cs = wit (suc (countFo LsetGraph)) packaged (c ∷ cs)

  -- W3 as the brief names it. UNBUILT. The hull carries no
  -- ordinality. Lset-only at src/L/Hierarchy.lagda.md:334-335
  -- needs IsOrd on the argument slot. That hypothesis does not
  -- arise on Code.

  lset-code : Type (ℓ-suc ℓ)
  lset-code =
    (c : Code) → Σ[ d ∈ Code ] (fst (val d) ≡ Lset (fst (val c)))

  -- D-10 correction beside the original. The consumer of levelIn
  -- has IsOrd. W3 as stated does not. Still unbuilt: feed still
  -- needs Vec Code (countFo LsetGraph), and the equality still
  -- needs Lset-only.

  lset-code-ord : Type (ℓ-suc ℓ)
  lset-code-ord =
    (c : Code) → IsOrd (fst (val c))
    → Σ[ d ∈ Code ] (fst (val d) ≡ Lset (fst (val c)))

  -- =====================================================================
  -- D-10 STEPS AS TYPES.  Step 1 is delivered. Step 3 is the meeting
  -- above, unbuilt as lset-code. Steps 2 and 4 are unbuilt. The
  -- obligation is omitted.
  -- =====================================================================

  Step1 : Type (ℓ-suc ℓ)
  Step1 = (z : S) → ⟨ z ∈ˢ C.πX ⟩
        → ∥ Σ[ y ∈ S ] (⟨ y ∈ˢ M ⟩ × (C.π y ≡ z)) ∥₁

  step1 : Step1
  step1 = C.πX-member

  HullClosedLset : Type (ℓ-suc ℓ)
  HullClosedLset =
    (y : S) → ⟨ y ∈ˢ M ⟩ → ⟨ Lset y ∈ˢ M ⟩

  πCommuteLset : Type (ℓ-suc ℓ)
  πCommuteLset =
    (y : S) → ⟨ y ∈ˢ M ⟩ → C.π (Lset y) ≡ Lset (C.π y)

  -- Step 4. Absoluteness. Same type as πCommuteLset. Unbuilt.

  -- The consumer's obligation. UNBUILT. Not a term named levelIn.
  LevelIn : Type (ℓ-suc ℓ)
  LevelIn =
    (δ : S) → IsOrd δ → ⟨ δ ∈ˢ C.πX ⟩ → ⟨ Lset δ ∈ˢ C.πX ⟩

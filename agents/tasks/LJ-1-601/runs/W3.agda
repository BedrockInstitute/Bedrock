{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.601]  W3.  THE STATEMENT, TYPE ONLY.
--
-- [LJ-1.597]'s reopener item 2, verbatim
-- (agents/tasks/LJ-1-597/review-of-step-graph.md:167-170):
--
--   "MEASURE THE FINITE BASE. No task has measured whether the `Tally`
--    route (`src/L/Choice/Finite`) has a formula. Ingredient (iv) cannot
--    be priced whole while its ω-base is unmeasured. That measurement is
--    smaller than this task was."
--
-- That sentence names a ROUTE and a QUESTION, not a type.  Stated at the
-- carrier this campaign's internalization reading already fixes, it is:
-- [LJ-1.597]'s own `Graph` shape (agents/tasks/LJ-1-597/Probe597.agda:
-- 269-285), a `Formula S 2` with value first and index second and BOTH
-- readings, at the FUNCTION PART of the route's delivered injection
-- `finite-stage-inj` (src/L/StageCardinal.lagda.md:485), read on the
-- members of the finite stage.  The two directions are the shape the
-- internalization chapter's own `Definition` demands, `defines` and
-- `only` (src/L/Recursion.lagda.md:272-279).
--
-- The brief: "Write it FIRST and typecheck it ALONE.  ESTIMATE: about
-- 12 lines, cap at two minutes."
--
-- CALIBER.  THE PROGRAM SET GHCRTS ON THIS PANE.  I DID NOT SET IT.
-- ONE AGDA PROCESS AT A TIME.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open import L.Constructible using ( IsOrd )
import Cubical.Data.Empty as Empty

module LJ-1-601.runs.W3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
  (α₀ : V ℓ) (oα₀ : IsOrd α₀)
  (sq : (δ : V ℓ) → ⟨ δ ∈ InfinitySet.sucV α₀ ⟩ → (⟨ δ ∈ InfinitySet.ω {ℓ} ⟩ → Empty.⊥)
      → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
          ((x y : ⟪ δ ⟫ × ⟪ δ ⟫) → f x ≡ f y → x ≡ y)) where

open import FOL.Syntax using ( Formula )
open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Presentation {ℓ} using ( member; fiber )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; Lset→isL )
open import L.Choice.Finite {ℓ} lem using ( finiteStage )
open import L.Ordinal {ℓ} using ( numeral-ord; ω-ord; suc-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.Axioms.Basic {ℓ} using ( LsetS )
import L.StageCardinal

open import Cubical.Data.Sigma using ( _×_ )
open Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫↪ )
open InfinitySet {ℓ} using ( ω; sucV; #_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
module SV = hPropStructure 𝒮ᵥ
module SL = hPropStructure 𝒮ʟ
open SV using ( _∈ˢ_ )
open SL using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

module SC = L.StageCardinal {ℓ} lem α₀ oα₀ sq
open SC using ( _↪_ )

-- 0.1  THE FINITE BASE, RE-ASCRIBED ALONE, TYPE ONLY.  The `Tally`
--      route's delivered injection at stage n
--      (src/L/StageCardinal.lagda.md:485): the members of the finite
--      stage `Lset (# n)`, injected into the members of `ω` by the
--      least tally index (the `FinInj` module, :448-484).  This row
--      names the type; the main probe measures the rest.
fin-base : (n : ℕ) → ⟪ finiteStage n ⟫ ↪ ⟪ ω ⟫
fin-base = SC.finite-stage-inj

-- 0.2  THE LIFTS, one line each.  [LJ-1.561]'s discipline
--      (agents/tasks/LJ-1-561/Probe561.agda:107-115 re-typed both
--      rather than import them): importing a probe costs its whole
--      elaboration and these are one line each.
isL-ord : (β : V ℓ) → IsOrd β → ⟨ isL β ⟩
isL-ord β oβ = Lset→isL (sucV β) (suc-ord oβ) β (ord∈Lset-suc β oβ)

up : (b : S) → ⟪ fst b ⟫ → S
up b m = ⟪ fst b ⟫↪ m , isL-trans (member (fst b) m) (snd b)

--      The domain and the codomain as L-elements.
dom : (n : ℕ) → S
dom n = LsetS (# n) (numeral-ord n)

ωS : S
ωS = ω , isL-ord ω ω-ord

--      The graph's subject: the finite base's function part, read on
--      the members of the domain through their presentations, lifted
--      to an L-element of `ω`.  `fst (dom n)` and `finiteStage n` are
--      the same term (`Lset (# n)`), so the membership below IS
--      membership in the finite stage.
val : (n : ℕ) (x : S) (m : ⟨ fst x ∈ fst (dom n) ⟩) → S
val n x m = up ωS (fst (fin-base n) (fiber (fst (dom n)) m .fst))

-- 0.3  THE STATEMENT.  THE OBLIGATION `finite-base-measured` IS THIS
--      TYPE AT EVERY n.  This slice states it and inhabits nothing:
--      the main probe `Probe601.agda` imports this module and builds
--      the term under this very type, so the stated statement and the
--      discharged one cannot drift.
TallyGraph : (n : ℕ) → Type (ℓ-suc ℓ)
TallyGraph n =
  Σ[ ψ ∈ Formula S 2 ]
    ( ((x y : S) (m : ⟨ fst x ∈ fst (dom n) ⟩)
       → fst y ≡ fst (val n x m) → ⟨ (y ∷ x ∷ []) ⊨ ψ ⟩)
    × ((x y : S) → ⟨ (y ∷ x ∷ []) ⊨ ψ ⟩ → (m : ⟨ fst x ∈ fst (dom n) ⟩)
       → fst y ≡ fst (val n x m)) )

finite-base-measured : (n : ℕ) → Type (ℓ-suc ℓ)
finite-base-measured n = TallyGraph n

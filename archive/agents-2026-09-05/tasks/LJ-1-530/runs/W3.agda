{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.530] W3, THE WIDEST UNMEASURED TERM, WRITTEN FIRST AND ALONE.
--
-- The brief names it: "whether a level holds its own definable
-- powerset, because that is the one step between [LJ-1.522]'s result
-- and this one", and the shape it asks for is
--
--     dpow-in-level : (α : V ℓ) → IsLimit α → (w : V ℓ) → ⟨ w ∈ Lset α ⟩
--                   → ⟨ 𝒟ₒ w ∈ Lset α ⟩
--
-- D-10 SAYS PRICE THE TRUTH BEFORE THE PROOF.  That statement is
-- written below as `BriefW3` and it is NOT INHABITED here.  The reason
-- is in the report; in one line, membership in `𝒟ₒ (Lset δ)` is "merely
-- some `defSet φ`" for ONE formula φ over ⟪ Lset δ ⟫
-- (src/L/Constructible.lagda.md:301-308), and the only formula that
-- carves `𝒟ₒ w` out of a level is `∃̇ (∃̇ (DefBody w))`
-- (src/L/Coding/Powerset.lagda.md:442-443), whose two existentials must
-- reach a code `keyS ψ` and a value `Sat A (toS ψ)` for EVERY ψ
-- (src/L/Coding/Powerset.lagda.md:643).  `Sat` is built by a recursion
-- that names the sub-formulas' own `Sat` sets as constants
-- (src/L/Coding/Sat.lagda.md:158-162), so nothing in the tree bounds
-- that family at one level below α.  I did not refute `BriefW3`.  I
-- report that the tree does not deliver it and that the obligation does
-- not need it.
--
-- THE CORRECTED TARGET, recorded beside the original as D-10 requires,
-- is the same statement with `w` a STAGE.  That is the only form the
-- tree states about a level and a definable powerset (`Lset-suc`,
-- src/L/Axioms/Basic.lagda.md:196), and it is the form the obligation's
-- own site supplies, because `Values`
-- (src/L/Hierarchy.lagda.md:117-119) says a recorded value IS a stage.
--
-- This file writes exactly that and nothing else.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth

module LJ-1-530.runs.W3 {ℓ : Level} where

open import FOL.Syntax using ( ⊤̇ )
open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Constructible {ℓ}
  using ( IsOrd; Lset; 𝒟ₒ; 𝒟ₒ-intro; Lset-in )
open import L.Axioms.Basic {ℓ} using ( Lset-suc )

open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; module InfinitySet )
open InfinitySet using ( sucV )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- The tree's notion of a limit level, verbatim from [LJ-1.522]
-- (agents/tasks/LJ-1-522/Probe522.agda:75-79).  A limit is said of the
-- INDEX and never of the stage.
IsLimit : V ℓ → Type (ℓ-suc ℓ)
IsLimit α = IsOrd α
          × ⟨ ∅ ∈ α ⟩
          × ((β : V ℓ) → ⟨ β ∈ α ⟩ → ⟨ sucV β ∈ α ⟩)

-- THE BRIEF'S W3, AS A TYPE ONLY.  Nothing below inhabits it.
BriefW3 : Type (ℓ-suc ℓ)
BriefW3 = (α : V ℓ) → IsLimit α → (w : V ℓ) → ⟨ w ∈ Lset α ⟩
        → ⟨ 𝒟ₒ w ∈ Lset α ⟩

-- A stage is a member of its own definable powerset: the formula "true"
-- selects everyone.  This is `isL-Lset`'s first line
-- (src/L/Axioms/Basic.lagda.md:157-158) with the `isL` wrapper dropped,
-- because the obligation needs the BOUND and not constructibility.
stage∈𝒟ₒ : (β : V ℓ) → ⟨ Lset β ∈ 𝒟ₒ (Lset β) ⟩
stage∈𝒟ₒ β = 𝒟ₒ-intro (Lset β) (Lset β)
  ∣ ⊤̇ , DefOf.defSet⊤≡A (Lset β) ∣₁

-- THE CORRECTED W3.  A limit level holds the definable powerset of
-- every STAGE below it.  Successor closure is the whole of the limit
-- that is spent: neither ordinality nor `∅ ∈ α` is used.
stage-dpow-in-level : (α : V ℓ) → IsLimit α → (δ : V ℓ) → ⟨ δ ∈ α ⟩
                    → ⟨ 𝒟ₒ (Lset δ) ∈ Lset α ⟩
stage-dpow-in-level α (_ , (_ , sc)) δ δ∈α =
  subst (λ u → ⟨ u ∈ Lset α ⟩) (Lset-suc δ)
    (Lset-in α (sucV δ) (Lset (sucV δ)) (sc δ δ∈α) (stage∈𝒟ₒ (sucV δ)))

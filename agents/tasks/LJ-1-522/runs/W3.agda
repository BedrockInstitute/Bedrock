{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.522] W3, THE WIDEST UNMEASURED TERM, WRITTEN FIRST AND ALONE.
--
-- The brief names it: "the limit reading, because everything turns on
-- it and [LJ-1.520] named it without measuring it", and the shape to
-- write is
--
--     limit-union : (K is a limit level)
--                 → (a member of K's definable powerset appears at some
--                    earlier level)
--
-- This file writes exactly that and nothing else.  If a limit level
-- does not decompose this way in this tree, the cure [LJ-1.520] named
-- is unavailable and the task stops at its cheapest point.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth

module LJ-1-522.runs.W3 {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; Lset; 𝒟ₒ; Lset-out )
open import L.Axioms.Basic {ℓ} using ( Lset-suc )
open import L.Ordinal {ℓ} using ( suc-ord; mem-ord )

open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; module InfinitySet )
open InfinitySet using ( sucV )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- THE TREE'S NOTION OF A LIMIT LEVEL, written where the carrier is a
-- value.  An ordinal, not zero, closed under the successor.  The tower
-- has no separate limit constructor: src/L/Constructible.lagda.md:16
-- says one equation covers zero, successors and limits at once, so the
-- limit has to be said of the INDEX and not of the stage.
IsLimit : S → Type (ℓ-suc ℓ)
IsLimit α = IsOrd α
          × ⟨ ∅ ∈ˢ α ⟩
          × ((β : S) → ⟨ β ∈ˢ α ⟩ → ⟨ sucV β ∈ˢ α ⟩)

-- W3.  AT A LIMIT THE STAGE IS THE UNION OF THE EARLIER STAGES.
-- Lset-out decomposes a member of Lset α as a member of the definable
-- powerset of an EARLIER stage (src/L/Constructible.lagda.md:336-338);
-- Lset-suc identifies that powerset with the NEXT stage
-- (src/L/Axioms/Basic.lagda.md:196); and the successor closure of a
-- limit puts that next index back inside α.
limit-union : (α : S) → IsLimit α → (x : S) → ⟨ x ∈ˢ Lset α ⟩
            → ∥ Σ[ δ ∈ S ] (IsOrd δ × ⟨ δ ∈ˢ α ⟩ × ⟨ x ∈ˢ Lset δ ⟩) ∥₁
limit-union α (oα , (_ , sc)) x x∈Lα = PT.map step (Lset-out α x x∈Lα)
  where
  step : Σ[ δ ∈ S ] (⟨ δ ∈ˢ α ⟩ × ⟨ x ∈ˢ 𝒟ₒ (Lset δ) ⟩)
       → Σ[ σ ∈ S ] (IsOrd σ × ⟨ σ ∈ˢ α ⟩ × ⟨ x ∈ˢ Lset σ ⟩)
  step (δ , (δ∈α , x∈𝒟ₒδ)) =
      sucV δ
    , ( suc-ord (mem-ord {A = α} oα δ δ∈α)
      , ( sc δ δ∈α
        , subst (λ w → ⟨ x ∈ˢ w ⟩) (sym (Lset-suc δ)) x∈𝒟ₒδ ) )

{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.572]  W3.  B9's `g`, ITS DEFINITION UNFOLDED.  TYPE ONLY.
--
-- THE BRIEF'S W3, VERBATIM: "the g at [LJ-1.561]'s w→B9 call site, its
-- definition unfolded, TYPE ONLY".  Written FIRST and typechecked
-- ALONE, before any other Agda of this task.  You cannot say a map is
-- definable before you have looked at the map.
--
-- [LJ-1.568]'s W3 (agents/tasks/LJ-1-568/runs/W3.agda:84-102) already
-- ascribed the map's TYPE.  THIS SLICE DOES THE OTHER HALF: it unfolds
-- the DEFINITION, and it does so by `refl` and not by quotation, so
-- the chain from `stage-card-upper` down to the module parameter `sq`
-- is CHECKED.
--
-- NOTHING BELOW IS A PROOF OF ANYTHING MISSING.  Every declaration is
-- an ASCRIPTION of a term already delivered in `src/`, a type, or a
-- `refl` that holds by a delivered definition.
--
-- CALIBER.  The program set GHCRTS on this pane.  I did not set it.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open import L.Constructible using ( IsOrd )
import Cubical.Data.Empty as Empty

module LJ-1-572.runs.W3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
  (α₀ : V ℓ) (oα₀ : IsOrd α₀)
  (sq : (δ : V ℓ) → ⟨ δ ∈ InfinitySet.sucV α₀ ⟩ → (⟨ δ ∈ InfinitySet.ω {ℓ} ⟩ → Empty.⊥)
      → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
          ((x y : ⟪ δ ⟫ × ⟪ δ ⟫) → f x ≡ f y → x ≡ y)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-induction )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; Lset; Lset→isL )
open import L.Ordinal {ℓ} using ( suc-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import L.Cardinal {ℓ} lem using ( _↪_ )
import L.StageCardinal

open import Cubical.Data.Sigma using ( _×_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫↪ )
open InfinitySet {ℓ} using ( sucV; ω )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))

module SV = hPropStructure 𝒮ᵥ
module SL = hPropStructure 𝒮ʟ
open SL using ( S )

module SC = L.StageCardinal {ℓ} lem α₀ oα₀ sq

-- [LJ-1.536]'s one-liner, re-typed the way Probe561.agda:110-111 does.
isL-ord : (β : V ℓ) → IsOrd β → ⟨ isL β ⟩
isL-ord β oβ = Lset→isL (sucV β) (suc-ord oβ) β (ord∈Lset-suc β oβ)

-- An ordinal as an L-element.  NAMED, exactly as Probe568.agda:100-101
-- names it, because the bare pair carries no expected type outside an
-- application and its second component blocks on a meta.
ordS : (β : V ℓ) → IsOrd β → S
ordS β oβ = β , isL-ord β oβ

-- ===================================================================
-- 1.  THE MAP, AT THE CARRIERS `w→B9` NAMES.
--     Probe561.agda:379-381 applies `w→code w (LsetS δ oδ)
--     (δ , isL-ord δ oδ)`, so `a` is `LsetS δ oδ`, `b` is `δ` and the
--     third argument is the `⟪ Lset δ ⟫ ↪ ⟪ δ ⟫` below.
-- ===================================================================

B9-g : (δ : V ℓ) (oδ : IsOrd δ) → ⟨ δ SV.∈ˢ sucV α₀ ⟩
     → (⟨ δ SV.∈ˢ ω ⟩ → Empty.⊥)
     → ⟪ fst (LsetS δ oδ) ⟫ ↪ ⟪ fst (ordS δ oδ) ⟫
B9-g = SC.Upper.stage-card-upper

-- ===================================================================
-- 2.  THE DEFINITION UNFOLDED.  THREE HOPS, EACH ONE `refl`.
--
--     src/L/StageCardinal.lagda.md:564-566 is the last line of the
--     chapter and the first hop below.  Nothing here is transcribed:
--     if a hop were wrong the file would not typecheck.
-- ===================================================================

-- HOP 1.  The map IS an ∈-recursion, and `step` is its body.
unfold-1 : SC.Upper.stage-card-upper ≡ ∈-induction SC.Upper.step
unfold-1 = refl

-- HOP 2.  `step`'s body is `limit-step` at the branch family.
unfold-2 : (α : V ℓ) (IH : (δ : V ℓ) → ⟨ δ SV.∈ˢ α ⟩ → SC.Upper.P δ)
           (oα : IsOrd α) (α∈suc : ⟨ α SV.∈ˢ sucV α₀ ⟩)
           (infα : ⟨ α SV.∈ˢ ω ⟩ → Empty.⊥)
         → SC.Upper.step α IH oα α∈suc infα
         ≡ SC.limit-step α α∈suc oα infα (SC.Upper.branch α oα α∈suc infα IH)
unfold-2 _ _ _ _ _ = refl

-- HOP 3.  AND THIS IS THE HOP THE TASK TURNS ON.  `limit-step` counts
--         the formulas of each earlier stage into `α`, and the counting
--         bound is `Bound α oα infα (sq α α∈suc infα)`
--         (src/L/StageCardinal.lagda.md:283, used at :287-292).  So the
--         value of the map at every stage is a value of `sq`.
--
--         `sq` IS A BARE MODULE PARAMETER.  It carries an injectivity
--         and NOTHING ELSE: no formula, no `isL`, no stage, no grade.
sq-bare : (δ : V ℓ) → ⟨ δ SV.∈ˢ sucV α₀ ⟩ → (⟨ δ SV.∈ˢ ω ⟩ → Empty.⊥)
        → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
            ((x y : ⟪ δ ⟫ × ⟪ δ ⟫) → f x ≡ f y → x ≡ y)
sq-bare = sq

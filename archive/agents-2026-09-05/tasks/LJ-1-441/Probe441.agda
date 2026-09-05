{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.441] W3 FIRST, then the obligation.  HALF A at the selected
-- arrow is a hole.  GraphOf is copied from
-- agents/tasks/LJ-1-414/Probe414.agda:56-63.  The four-projection seal
-- is copied from agents/tasks/LJ-1-433/Probe433.agda:79-90.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber,
-- set on the pane by the program and untouched here.
-- Nothing lands in src/.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-441.Probe441 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd )
open import L.Cardinal {ℓ} lem using ( InjCode; _↪_; module LeastCardInjL )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( ω; sucV )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )
open hPropStructure 𝒮ʟ using ( S )

-- =====================================================================
-- GraphOf, copied from Probe414.agda:56-63.  Not imported.
-- =====================================================================

GraphOf : (x d : S) → (⟪ fst x ⟫ ↪ ⟪ fst d ⟫) → S → Type (ℓ-suc ℓ)
GraphOf x d f G =
    ((u v : S) → ⟨ pr (fst u) (fst v) ∈ fst G ⟩
               → ∥ Σ[ m ∈ ⟪ fst x ⟫ ]
                    ((fst u ≡ ⟪ fst x ⟫↪ m)
                   × (fst v ≡ ⟪ fst d ⟫↪ (fst f m))) ∥₁)
  × ((m : ⟪ fst x ⟫)
      → ⟨ pr (⟪ fst x ⟫↪ m) (⟪ fst d ⟫↪ (fst f m)) ∈ fst G ⟩)

-- =====================================================================
-- The ambient least cardinal, sealed at the call site (P-i, R-36).
-- Same four projections as Probe433.agda:79-90.
-- =====================================================================

opaque
  κL : (a : S) (oa : IsOrd (fst a)) → S
  κL a oa = LeastCardInjL.κ a oa

  κoL : (a : S) (oa : IsOrd (fst a)) → IsOrd (fst (κL a oa))
  κoL a oa = LeastCardInjL.oκ a oa

  κ∈sucL : (a : S) (oa : IsOrd (fst a)) → ⟨ fst (κL a oa) ∈ sucV (fst a) ⟩
  κ∈sucL a oa = LeastCardInjL.κ∈sα a oa

  κ-injL : (a : S) (oa : IsOrd (fst a)) → ∥ ⟪ fst a ⟫ ↪ ⟪ fst (κL a oa) ⟫ ∥₁
  κ-injL a oa = LeastCardInjL.κ-inj a oa

-- =====================================================================
-- W3.  HALF A at the selected arrow.  PT.rec on κ-injL is legal: the
-- goal is a truncation.  The remaining hole is GraphOf at the opened
-- arrow.  Stated first, with the obligation omitted, then kept.
-- =====================================================================

half-a-at-least :
    (a : S) (oa : IsOrd (fst a)) → ⟨ fst (κL a oa) ∈ˢ fst a ⟩
  → ∥ Σ[ f ∈ (⟪ fst a ⟫ ↪ ⟪ fst (κL a oa) ⟫) ]
        (Σ[ G ∈ S ] GraphOf a (κL a oa) f G) ∥₁
half-a-at-least a oa κ∈a =
  PT.rec squash₁ from-down (κ-injL a oa)
  where
  from-down : (⟪ fst a ⟫ ↪ ⟪ fst (κL a oa) ⟫)
            → ∥ Σ[ f ∈ (⟪ fst a ⟫ ↪ ⟪ fst (κL a oa) ⟫) ]
                  (Σ[ G ∈ S ] GraphOf a (κL a oa) f G) ∥₁
  from-down f = ∣ f , graph-of-f ∣₁
    where
    graph-of-f : Σ[ G ∈ S ] GraphOf a (κL a oa) f G
    graph-of-f = {!!}

-- =====================================================================
-- THE OBLIGATION.  Route 1: PT.rec on κ-injL (legal: the goal is a
-- truncation), then HALF A at the opened arrow.  That is the hole.
-- HALF B is Probe414.agda:115-128, green, not imported: it consumes
-- the graph the hole does not supply.  Route 2 is not a term: κ-min-at
-- (src/L/Cardinal.lagda.md:140-141) refutes a smaller injection and
-- does not name a graph.  See review-of-amb-to-coded-at-least.md.
-- =====================================================================

amb-to-coded-at-least :
    (a : S) (oa : IsOrd (fst a)) → ⟨ ω ∈ˢ fst a ⟩
  → ⟨ fst (κL a oa) ∈ˢ fst a ⟩
  → (⟨ fst (κL a oa) ∈ˢ ω ⟩ → Empty.⊥)
  → ∥ Σ[ F ∈ S ] InjCode F a (κL a oa) ∥₁
amb-to-coded-at-least a oa ω∈a κ∈a κ∉ω =
  PT.rec squash₁ from-down (κ-injL a oa)
  where
  from-down : (⟪ fst a ⟫ ↪ ⟪ fst (κL a oa) ⟫)
            → ∥ Σ[ F ∈ S ] InjCode F a (κL a oa) ∥₁
  from-down f = {!!}

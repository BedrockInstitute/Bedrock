{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.603]  INGREDIENT (iv) AT THE INFINITE MEMBER STAGES.
--
-- VERDICT: NO-GO.  agents/tasks/LJ-1-603/review-of-rec-graph-at-infinite.md
-- states it and names the atom: THE LIMIT CASE REACHES `sq`.  **THE
-- OBLIGATION `rec-graph-at-infinite` IS NOT IN THIS FILE** and no weaker
-- term is offered as one: that is [LJ-1.597]'s discipline
-- (agents/tasks/LJ-1-597/Probe597.agda:5-8).  This file carries NO hole
-- and NO postulate, so every row in it is a measurement and not a
-- claim.  Nothing lands in `src/`.
--
-- W3 IS agents/tasks/LJ-1-603/runs/W3.agda AND IT WAS WRITTEN FIRST AND
-- TYPECHECKED ALONE (`runs/w3-2.out`, GREEN, 1.42 s, cap 120 s; the
-- record spelling of the same index WALLS the pane's 2 GB, four runs,
-- `runs/w3-1.out` and `runs/bisect-a.out` to `bisect-c.out`, and the
-- Sigma spelling is the cure `runs/bisect-d.out` measured, 1.32 s).
-- It is IMPORTED below, not restated, and so is [LJ-1.601]'s table
-- term: R-42's respelling price, as the brief states it.
--
--   Section 0.  W3, imported, and the statement's shape.
--   Section 1.  THE VALUE EQUATION AT AN INFINITE MEMBER STAGE, seven
--               `refl` rows.  [LJ-1.594]'s discipline, one stage down:
--               every row is at the MEMBER stage `δ`, where [LJ-1.594]
--               wrote its rows at the ambient stage `α`.  Rows 1.3,
--               1.4 and 1.7 are the `sq` arrival, measured.
--   Section 2.  THE FINITE BASE BESIDE IT, imported, one row.  The two
--               halves of ingredient (iv) compose at one type with no
--               respelling: [LJ-1.601]'s table term at [LJ-1.601]'s own
--               statement, under this pane's parameters.
--   Section 3.  THE BRANCH'S LIMIT CASE, TYPE ONLY, and `P` is the
--               injection: the reading that ties section 1 to
--               ingredient (iv), with its sites named.
--   Section 4.  THE OBLIGATION'S TYPE, stated by import and NOT
--               inhabited.  The stop file carries the verdict.
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

module LJ-1-603.runs.BisectG {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
  (α₀ : V ℓ) (oα₀ : IsOrd α₀)
  (sq : (δ : V ℓ) → ⟨ δ ∈ InfinitySet.sucV α₀ ⟩ → (⟨ δ ∈ InfinitySet.ω {ℓ} ⟩ → Empty.⊥)
      → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
          ((x y : ⟪ δ ⟫ × ⟪ δ ⟫) → f x ≡ f y → x ≡ y)) where

open import FOL.Syntax using ( Formula )
open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( Lset; 𝒟ₒ; 𝒟ₒ-inv )
open import L.Definability {ℓ} using ( module DefOf )
open import FOL.Count {ℓ} using ( composed-count; code )
open import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ} using ( leastOf )
import L.StageCardinal

open import Cubical.Data.Nat using ( ℕ )
open import Cubical.Data.Sigma using ( _×_ )
open import Cubical.Data.Vec using ( Vec )
open Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫↪ )
open InfinitySet {ℓ} using ( ω; sucV )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
module SV = hPropStructure 𝒮ᵥ
open SV using ( _∈ˢ_ )

module SC = L.StageCardinal {ℓ} lem α₀ oα₀ sq
open SC using ( _↪_ )

-- THE STATEMENT, imported from the slice that typechecked it alone.
import LJ-1-603.runs.W3 {ℓ} lem α₀ oα₀ sq as W3


-- 1.1  THE STEP AT THE MEMBER STAGE IS `LimitStep.h` AT IT, with the
--      site's `D` and `inv` supplied.  [LJ-1.594]'s `D-at-the-site`
--      (Probe594.agda:227-234), one stage down.
step-at-member :
    (δ : V ℓ) (δ∈suc : ⟨ δ ∈ˢ sucV α₀ ⟩) (oδ : IsOrd δ)
    (infδ : ⟨ δ ∈ˢ ω ⟩ → Empty.⊥)
    (ih : (m : ⟪ δ ⟫) → ⟪ Lset (⟪ δ ⟫↪ m) ⟫ ↪ ⟪ δ ⟫)
  → fst (SC.limit-step δ δ∈suc oδ infδ ih)
    ≡ SC.LimitStep.h δ δ∈suc oδ infδ (λ ε φ → DefOf.defSet (Lset ε) φ)
        (λ ε y h → 𝒟ₒ-inv (Lset ε) y h) ih
step-at-member _ _ _ _ _ = refl

-- 1.2  THE VALUE IS THE ORDINAL-LEAST WITNESS.  [LJ-1.594]'s
--      `h-is-leastOf` (Probe594.agda:305-317), one stage down.
value-is-leastOf :
    (δ : V ℓ) (δ∈suc : ⟨ δ ∈ˢ sucV α₀ ⟩) (oδ : IsOrd δ)
    (infδ : ⟨ δ ∈ˢ ω ⟩ → Empty.⊥)
    (D : (ε : V ℓ) → Formula ⟪ Lset ε ⟫ 1 → V ℓ)
    (inv : (ε : V ℓ) (y : V ℓ) → ⟨ y ∈ˢ 𝒟ₒ (Lset ε) ⟩
         → ∥ Σ[ φ₀ ∈ Formula ⟪ Lset ε ⟫ 1 ] (D ε φ₀ ≡ y) ∥₁)
    (ih : (m : ⟪ δ ⟫) → ⟪ Lset (⟪ δ ⟫↪ m) ⟫ ↪ ⟪ δ ⟫)
    (x : ⟪ Lset δ ⟫)
  → SC.LimitStep.h δ δ∈suc oδ infδ D inv ih x
    ≡ fst (leastOf (SC.OrdSWO.ordSWO δ oδ) lem
             (SC.LimitStep.class-pred δ δ∈suc oδ infδ D inv ih x)
             (SC.LimitStep.nonempty δ δ∈suc oδ infδ D inv ih x))
value-is-leastOf _ _ _ _ _ _ _ _ = refl

-- 1.3  **THE ROW: THE CLASS, WRITTEN OUT, AND THE VALUE SITS ON THE
--      `sq`-APPLICATION SIDE.**  [LJ-1.594]'s `class-pred-is`
--      (Probe594.agda:283-300), one stage down.  READ THE RIGHT HAND
--      SIDE: the second conjunct of the witness is
--          `fst (sq δ δ∈suc infδ) (m , cnt m φ) ≡ y`,
--      and y occurs NOWHERE ELSE.  A `Formula` for this graph must
--      express THAT equation, and `sq` is the bare module parameter
--      (src/L/StageCardinal.lagda.md:17-20): injectivity and nothing
--      else, no formula, no Levy grade, no stage.
class-pred-at-member :
    (δ : V ℓ) (δ∈suc : ⟨ δ ∈ˢ sucV α₀ ⟩) (oδ : IsOrd δ)
    (infδ : ⟨ δ ∈ˢ ω ⟩ → Empty.⊥)
    (D : (ε : V ℓ) → Formula ⟪ Lset ε ⟫ 1 → V ℓ)
    (inv : (ε : V ℓ) (y : V ℓ) → ⟨ y ∈ˢ 𝒟ₒ (Lset ε) ⟩
         → ∥ Σ[ φ₀ ∈ Formula ⟪ Lset ε ⟫ 1 ] (D ε φ₀ ≡ y) ∥₁)
    (ih : (m : ⟪ δ ⟫) → ⟪ Lset (⟪ δ ⟫↪ m) ⟫ ↪ ⟪ δ ⟫)
    (x : ⟪ Lset δ ⟫) (y : ⟪ δ ⟫)
  → SC.LimitStep.class-pred δ δ∈suc oδ infδ D inv ih x y
    ≡ ( ∥ Σ[ m ∈ ⟪ δ ⟫ ] Σ[ φ ∈ Formula ⟪ Lset (⟪ δ ⟫↪ m) ⟫ 1 ]
            ( ( D (⟪ δ ⟫↪ m) φ ≡ ⟪ Lset δ ⟫↪ x )
            × ( fst (sq δ δ∈suc infδ)
                  ( m
                  , SC.LimitStep.cnt δ δ∈suc oδ infδ D inv ih m φ )
                ≡ y ) ) ∥₁
      , squash₁ )
class-pred-at-member _ _ _ _ _ _ _ _ _ = refl

-- (rows 1.4 to 1.7, sections 2 to 4 removed for bisection)

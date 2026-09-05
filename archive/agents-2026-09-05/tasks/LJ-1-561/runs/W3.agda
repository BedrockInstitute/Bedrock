{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.561]  W3.  THE FIVE MISSING PIECES, SIDE BY SIDE, TYPE ONLY.
--
-- THE QUESTION THIS FILE ANSWERS, AND IT ANSWERS NOTHING ELSE:
-- can the five statements the five stopped dispatches named be written
-- in ONE file at all?  If they cannot sit together, every later claim
-- about them is unmeasurable.
--
-- NO TERM BELOW IS A PROOF OF A MISSING PIECE.  Every declaration is a
-- TYPE, or a name for a term ALREADY DELIVERED in src/ that this file
-- only ASCRIBES, so that the starting point of each site is checked and
-- not quoted.
--
-- THE FRAME QUESTION IS THIS SLICE'S FINDING.  Four of the five sites
-- live at `{ℓ} (lem)` alone.  ONE does not: [LJ-1.535]'s site is inside
-- `L.StageCardinal`, whose three parameters (α₀, oα₀, sq) are module
-- parameters and cannot be discharged (src/L/StageCardinal.lagda.md:15-19).
-- So this file TAKES them, the way agents/tasks/LJ-1-535/Probe535.agda:59-63
-- does, and the other four statements never mention them.
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

module LJ-1-561.runs.W3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
  (α₀ : V ℓ) (oα₀ : IsOrd α₀)
  (sq : (δ : V ℓ) → ⟨ δ ∈ InfinitySet.sucV α₀ ⟩ → (⟨ δ ∈ InfinitySet.ω {ℓ} ⟩ → Empty.⊥)
      → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
          ((x y : ⟪ δ ⟫ × ⟪ δ ⟫) → f x ≡ f y → x ≡ y)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
import FOL.Absoluteness
import FOL.ZFModel
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import V.Presentation {ℓ} using ( fiber )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; Lset; Lset→isL )
open import L.Ordinal {ℓ} using ( suc-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import L.Hierarchy {ℓ} lem using ( hierL )
open import L.Cardinal {ℓ} lem using ( InjCode; _↪_ )
open import L.GCH {ℓ} lem using ( InjL; SuccCardL )
import L.CantorBernstein
import L.StageCardinal

open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫↪ )
open InfinitySet {ℓ} using ( sucV; ω )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))

module SV = hPropStructure 𝒮ᵥ
module SL = hPropStructure 𝒮ʟ
open SL using ( S )

module ModelL = FOL.ZFModel 𝒮ʟ
open ModelL using ( _⊆ˢ_ )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- The delivered chapter, at this pane's parameters.  NOT rebuilt.
module SC = L.StageCardinal {ℓ} lem α₀ oα₀ sq
module CB = L.CantorBernstein {ℓ} lem

-- Two one-liners the five statements need.  Both are [LJ-1.536]'s and
-- [LJ-1.549]'s, re-typed here so this slice imports no probe.
isL-ord : (β : V ℓ) → IsOrd β → ⟨ isL β ⟩
isL-ord β oβ = Lset→isL (sucV β) (suc-ord oβ) β (ord∈Lset-suc β oβ)

ixOf : (δ x : S) → ⟨ fst x SV.∈ˢ fst δ ⟩ → ⟪ fst δ ⟫
ixOf δ x m = fiber (fst δ) m .fst


-- ===================================================================
-- THE FIVE, IN THE ORDER THE BRIEF TABULATES THEM.
-- ===================================================================

-- 1.  B9, `StageCountedCoded`, stopped by [LJ-1.533].
--     WHAT IT COULD NOT GET: a code for an ambient injection
--     ⟪ Lset δ ⟫ ↪ ⟪ δ ⟫.
--
--     STATED AT [LJ-1.533]'s CORRECTED TARGET AND NOT AT THE BRIEF'S.
--     agents/tasks/LJ-1-533/review-of-StageCountedCoded.md:22-52 refuted
--     the unrestricted form: with no infinitude hypothesis the type
--     lands the ambient statement at every finite ordinal, which
--     src/L/StageCardinal.lagda.md:488-490 refuses.  The two extra
--     hypotheses below are exactly `stage-card-upper`'s own.
Missing-B9 : Type (ℓ-suc ℓ)
Missing-B9 =
    (δ : V ℓ) (oδ : IsOrd δ) → ⟨ δ SV.∈ˢ sucV α₀ ⟩ → (⟨ δ SV.∈ˢ ω ⟩ → Empty.⊥)
  → InjL (LsetS δ oδ) (δ , isL-ord δ oδ)

-- AND THE AMBIENT HALF IS DELIVERED.  src/L/StageCardinal.lagda.md:564-565.
delivered-B9 : (δ : V ℓ) → IsOrd δ → ⟨ δ SV.∈ˢ sucV α₀ ⟩
             → (⟨ δ SV.∈ˢ ω ⟩ → Empty.⊥) → ⟪ Lset δ ⟫ ↪ ⟪ δ ⟫
delivered-B9 = SC.Upper.stage-card-upper


-- 2.  B7, THE COUNTING SITE, stopped by [LJ-1.535].
--     WHAT IT COULD NOT GET: a code out of a bare Σ.
--     agents/tasks/LJ-1-535/review-of-stage-card-upper-coded.md:40-52
--     names the bare Σ as `_↪_` itself (src/L/Cardinal.lagda.md:47-48).
Missing-B7 : Type (ℓ-suc ℓ)
Missing-B7 = (a b : S) → ⟪ fst a ⟫ ↪ ⟪ fst b ⟫ → InjL a b


-- 3.  `Link`, THE RESIDUE'S FOURTH COMPONENT, stopped by [LJ-1.549]
--     and [LJ-1.554].
--     WHAT IT COULD NOT GET: a formula describing an ambient assignment.
--     The type is agents/tasks/LJ-1-554/Probe554.agda:88-93, restated.
Missing-Link : Type (ℓ-suc ℓ)
Missing-Link =
    (δ κ : S) (s : ⟪ fst δ ⟫ → S)
  → ((k : ⟪ fst δ ⟫) → ⟨ s k ⊆ˢ κ ⟩)
  → ((k k' : ⟪ fst δ ⟫) → fst (s k) ≡ fst (s k') → k ≡ k')
  → Σ[ Link ∈ Formula S 3 ]
      ( ((x y z : S) (m : ⟨ fst x SV.∈ˢ fst δ ⟩) → fst y ≡ fst (s (ixOf δ x m))
         → ⟨ (y ∷ x ∷ z ∷ []) ⊨ Link ⟩)
      × ((x y z : S) → ⟨ (y ∷ x ∷ z ∷ []) ⊨ Link ⟩
         → (m : ⟨ fst x SV.∈ˢ fst δ ⟩) → fst y ≡ fst (s (ixOf δ x m))) )


-- 4.  THE ASSIGNMENT, stopped by [LJ-1.552].
--     WHAT IT COULD NOT GET: an L-set out of an ambient injection.
--     The type is agents/tasks/LJ-1-552/Probe552.agda:109-113, restated.
Missing-Assignment : Type (ℓ-suc ℓ)
Missing-Assignment =
    (δ κ : S) → SuccCardL δ κ
  → ∥ Σ[ s ∈ (⟪ fst δ ⟫ → S) ]
        ( ((k : ⟪ fst δ ⟫) → ⟨ s k ⊆ˢ κ ⟩)
        × ((k k' : ⟪ fst δ ⟫) → fst (s k) ≡ fst (s k') → k ≡ k') ) ∥₁


-- 5.  `StageHigh`, stopped by [LJ-1.536].
--     WHAT IT COULD NOT GET: a `Formula ⟪ A ⟫ 1` for `𝒟ₒ-intro`.
--
--     STATED AS [LJ-1.536]'s OWN RESIDUE AND NOT AS ITS OBLIGATION.
--     `StageHigh` itself is DISCHARGED there, total in γ, by
--     `reduction` (agents/tasks/LJ-1-536/Probe536.agda:357-358) from
--     `HierBelowAll`; and `HierBelow` at a SUCCESSOR is that same
--     conclusion one step down (:367-371).  What is left unpaid is the
--     limit case, agents/tasks/LJ-1-536/Probe536.agda:405-409.
Missing-StageHigh : Type (ℓ-suc ℓ)
Missing-StageHigh =
    (γ : V ℓ) (oγ : IsOrd γ) → ((δ : V ℓ) → ⟨ δ ∈ γ ⟩ → ⟨ sucV δ ∈ γ ⟩)
  → ⟨ fst (hierL γ (isL-ord γ oγ) oγ) ∈ Lset (sucV (sucV (sucV γ))) ⟩


-- ===================================================================
-- AND THE CANDIDATE, BESIDE THEM, TYPE ONLY.
--
-- W says: the graph of an ambient injection between the members of two
-- sets of L is itself a set of L.  It names no formula, no grade and no
-- stage.
-- ===================================================================

IsGraph : (a b : S) (g : ⟪ fst a ⟫ → ⟪ fst b ⟫) (G : S) → Type (ℓ-suc ℓ)
IsGraph a b g G =
    ((k : ⟪ fst a ⟫) → ⟨ pr (⟪ fst a ⟫↪ k) (⟪ fst b ⟫↪ (g k)) SV.∈ˢ fst G ⟩)
  × ((x y : S) → ⟨ pr (fst x) (fst y) SV.∈ˢ fst G ⟩
       → ∥ Σ[ k ∈ ⟪ fst a ⟫ ]
             ((fst x ≡ ⟪ fst a ⟫↪ k) × (fst y ≡ ⟪ fst b ⟫↪ (g k))) ∥₁)

W : Type (ℓ-suc ℓ)
W = (a b : S) (g : ⟪ fst a ⟫ → ⟪ fst b ⟫)
  → ((k k' : ⟪ fst a ⟫) → g k ≡ g k' → k ≡ k')
  → ∥ Σ[ G ∈ S ] IsGraph a b g G ∥₁

-- W IS THE CONVERSE OF A DELIVERED TERM, AND THIS IS THAT TERM.
-- `readL` (src/L/CantorBernstein.lagda.md:33-38) turns a code into an
-- ambient injection.  Nothing in the tree goes the other way.
delivered-converse : (a b : S) → InjL a b → ∥ ⟪ fst a ⟫ ↪ ⟪ fst b ⟫ ∥₁
delivered-converse a b = PT.map (CB.readL a b)

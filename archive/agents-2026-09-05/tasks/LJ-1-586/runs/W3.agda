{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.586]  W3, THE WIDEST UNMEASURED TERM: `absorbs`, PARAMETER OR
-- TERM.  Typechecked ALONE before any other Agda in this task.
--
-- THE GREP HALF IS THE ANSWER AND THE AGDA HALF IS ITS CHECK.
-- `grep -rn "BoundedSubsetAt" src/` gives THREE lines and ONE of them
-- is a module application:
--
--   src/L/BoundedSubset.lagda.md:1385   module BoundedSubsetAt          the declaration
--   src/L/StageBound.lagda.md:62        a comment
--   src/L/StageBound.lagda.md:74        module BSA = Devlin55.BoundedSubsetAt ...   THE ONLY APPLICATION
--
-- Its twelfth argument is `absorbs` (src/L/StageBound.lagda.md:76),
-- and that name is the enclosing module's OWN parameter
-- (src/L/StageBound.lagda.md:69).  The outer wrapper repeats the same
-- pass-through (:97 declared, :116 forwarded).  `L.StageBound` is
-- imported by ONE file, `src/Everything.lagda.md:396`, which only
-- typechecks it.
--
-- SO THE COUNT OF CONCRETE TERMS SUPPLIED FOR THE TWELFTH PARAMETER IN
-- `src/` IS **ZERO**.  `absorbs` is ONLY EVER A PARAMETER there.
-- `src/L/Absorption.lagda.md:635` carries the NAME at a different type,
-- `⟪ sucV (fst γ) ⟫ ↪ ⟪ fst γ ⟫`, and does not fit the slot (C-42: it
-- is a different statement and this file never reads one as the other).
--
-- THE AGDA HALF.  A parameter with no term is one thing; a parameter
-- with a DELIVERED inhabitant that `src/` has not yet plugged in is
-- another, and the two need different briefs.  Section W3.2 ascribes
-- `[LJ-1.540]`'s `AbsorbsAt` AT THE TWELFTH PARAMETER'S TYPE, letter
-- for letter from src/L/BoundedSubset.lagda.md:1392.  If it typechecks,
-- the slot has a candidate and the obligation is a description of THAT.
--
-- W3.3 is the second half: `Def` lives at L-SETS and `absorbs` lives at
-- AMBIENT sets, so the pair (domain , codomain) must be shown to be
-- L-elements before `Def` can even be STATED at this `g`.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-586.runs.W3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; IsOrd; Lset; isL; isL-trans; Lset→isL; 𝒟ₒ-intro; Lset-in )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Ordinal {ℓ} using ( suc-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.BoundedSubset {ℓ} lem using ( _↪_ )
open import L.Coding.InL {ℓ} using ( sglL; cupL )
open import V.Model {ℓ} using ( self∈sucV )
open import FOL.Syntax using ( ⊤̇ )

open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; _∪_; ⁅_⁆s )
open InfinitySet {ℓ} using ( ω; sucV )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
module SV = hPropStructure 𝒮ᵥ
module SL = hPropStructure 𝒮ʟ
open SV using ( S; _∈ˢ_ )

import LJ-1-540.Probe540 {ℓ} lem as P540


-- =====================================================================
-- W3.1  THE SLOT'S TYPE, COPIED FROM THE PARAMETER LIST AND NOTHING
--       ELSE.  src/L/BoundedSubset.lagda.md:1391-1392.
-- =====================================================================

Slot : (α x : S) → Type ℓ
Slot α x = ⟪ Lset α ∪ ⁅ x ⁆s ⟫ ↪ ⟪ Lset α ⟫


-- =====================================================================
-- W3.2  THE SLOT HAS A DELIVERED INHABITANT, AND IT IS NOT IN `src/`.
--       `[LJ-1.540]`'s `AbsorbsAt` (agents/tasks/LJ-1-540/Probe540.agda
--       :359-365), ascribed AT `Slot`.  The elaborator's word, not the
--       report's.
-- =====================================================================

candidate : (α x : S) → IsOrd α → (⟨ α ∈ˢ ω ⟩ → Empty.⊥)
          → ((z : S) → ⟨ z ∈ˢ x ⟩ → ⟨ z ∈ˢ Lset α ⟩)
          → Slot α x
candidate = P540.AbsorbsAt

-- AND IT NEEDS ONLY THREE OF THE FOUR.  `[LJ-1.540]`'s own surplus
-- measurement (Probe540.agda:371-376) at `Slot`.
candidate-no-subset : (α x : S) → IsOrd α → (⟨ α ∈ˢ ω ⟩ → Empty.⊥) → Slot α x
candidate-no-subset = P540.absorbs-needs-no-subset-hypothesis


-- =====================================================================
-- W3.3  THE PAIR `Def` WOULD BE STATED AT, AS L-ELEMENTS.
--
--   `[LJ-1.568]`'s `Def` is `Hyp = (a b : Sʟ) (g : ⟪ fst a ⟫ → ⟪ fst b ⟫)
--   → Type` (Probe568.agda:158-159).  `absorbs` is a map between the
--   members of two AMBIENT sets.  So before `Def` can be STATED here,
--   `Lset α` and `Lset α ∪ ⁅ x ⁆s` must both be L-elements.
--
--   The stage is `[LJ-1.580]`'s `Lset-isL` (Probe580.agda:104-107),
--   re-typed rather than imported because importing Probe580 costs its
--   whole site telescope and this file needs four lines of it.
--   The union is TWO library facts already in `src/`:
--   `sglL` and `cupL` (src/L/Coding/InL.lagda.md:206, :211).
-- =====================================================================

Lset-isL : (γ : S) → IsOrd γ → ⟨ isL (Lset γ) ⟩
Lset-isL γ oγ = Lset→isL (sucV γ) (suc-ord oγ) (Lset γ)
  (Lset-in (sucV γ) γ (Lset γ) (self∈sucV γ)
    (𝒟ₒ-intro (Lset γ) (Lset γ) ∣ ⊤̇ , DefOf.defSet⊤≡A (Lset γ) ∣₁))

-- THE DOMAIN IS AN L-ELEMENT.  `x` is one because it is a member of a
-- stage, which is the site's own `x∈Lλ`
-- (src/L/BoundedSubset.lagda.md:1395).
dom-isL : (α lam x : S) → IsOrd α → IsOrd lam → ⟨ x ∈ˢ Lset lam ⟩
        → ⟨ isL (Lset α ∪ ⁅ x ⁆s) ⟩
dom-isL α lam x oα oλ x∈Lλ =
  cupL (Lset-isL α oα) (sglL (Lset→isL lam oλ x x∈Lλ))

-- THE TWO L-SETS, PACKED.  `Dᴸ` is `UnionKit.X`
-- (src/L/BoundedSubset.lagda.md:1148) with its level-hood.
module Pair (α lam x : S) (oα : IsOrd α) (oλ : IsOrd lam)
            (x∈Lλ : ⟨ x ∈ˢ Lset lam ⟩) where

  Dᴸ : SL.S
  Dᴸ = Lset α ∪ ⁅ x ⁆s , dom-isL α lam x oα oλ x∈Lλ

  Cᴸ : SL.S
  Cᴸ = Lset α , Lset-isL α oα

  -- AND THE SLOT'S FUNCTION IS A MAP BETWEEN THEIR MEMBERS, WHICH IS
  -- WHAT `Hyp` DEMANDS.  `refl`-free: this is a type ascription.
  as-Hyp-g : (α∉ω : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
           → ((z : S) → ⟨ z ∈ˢ x ⟩ → ⟨ z ∈ˢ Lset α ⟩)
           → ⟪ fst Dᴸ ⟫ → ⟪ fst Cᴸ ⟫
  as-Hyp-g α∉ω x⊆Lα = fst (P540.AbsorbsAt α x oα α∉ω x⊆Lα)

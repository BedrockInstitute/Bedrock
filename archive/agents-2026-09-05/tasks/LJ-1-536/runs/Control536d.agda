{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.536] PROBE.  StageHigh, which four routes have arrived at.
-- It runs in agents/tasks/LJ-1-536/ and lands nothing in src/.
--
--   D-10, FIRST    what `𝒟ₒ-intro` wants, and whether [LJ-1.520]'s
--                  graded formula is that formula.  Sections 1 and 2.
--   W3, SECOND     runs/W3.agda, written and typechecked ALONE before
--                  this file existed.  Sections 1 to 3 rerun its terms
--                  so that the finding and the obligation stand in one
--                  file.
--   OBLIGATION     StageHigh.  Section 6 states it.  Section 5 reduces
--                  it, GREEN and total in γ, to one statement about the
--                  sequence BELOW γ.  Section 7 says what is left.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-536.runs.Control536d {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _∈̇_; _≐_; _∨̇_; ⊤̇ )
open import FOL.LevyHierarchy using ( Δ₀; Σ₁ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Model {ℓ} using ( self∈sucV; ∈sucV-inl; ∈sucV-elim )
open import V.Coding {ℓ} using ( pr )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; Lset-layer; layer-trans
        ; Lset-mono; Lset→isL; 𝒟ₒ; 𝒟ₒ-intro )
open import L.Ordinal {ℓ} using ( suc-ord; ω-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.Axioms.Basic {ℓ} using ( Lset-suc; pr∈Lset-suc )
open import L.Hierarchy {ℓ} lem using ( hierL; hierL-spec; IsHier; Recorded )
open import LJ-1-520.Probe520 {ℓ} lem using ( levelFo-Σ₁ )

open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; ∈∈ₛ; ∈-asFiber; extensionality; _⊆_; ⟪_⟫; ⟪_⟫↪; ∈ₛ⟪_⟫↪_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( sucV; ω )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ


step : ℕ → V ℓ → V ℓ
step zero    γ = γ
step (suc n) γ = sucV (step n γ)

-- An ordinal is an element of L, because it appears at the stage after
-- itself (src/L/Ordinal/Stages.lagda.md:434) and stages are inside L
-- (src/L/Constructible.lagda.md:395).
isL-ord : (β : V ℓ) → IsOrd β → ⟨ isL β ⟩
isL-ord β oβ = Lset→isL (sucV β) (suc-ord oβ) β (ord∈Lset-suc β oβ)

-- Devlin's (L_δ | δ ≤ γ): the internal hierarchy at sucV γ, because
-- sucV γ is exactly the ordinals δ ≤ γ.
-- agents/tasks/LJ-1-519/Probe519.agda:137.
seq : (γ : V ℓ) → IsOrd γ → S
seq γ oγ = hierL (sucV γ) (isL-ord (sucV γ) (suc-ord oγ)) (suc-ord oγ)

seq-spec : (γ : V ℓ) (oγ : IsOrd γ) → IsHier (sucV γ) (seq γ oγ)
seq-spec γ oγ = hierL-spec (sucV γ) (isL-ord (sucV γ) (suc-ord oγ)) (suc-ord oγ)


-- ===================================================================
-- SECTION 4.  WHERE ONE RECORDED PAIR LIVES.
--
-- A stage is a member of the next stage, and an ordinal is too, so the
-- Kuratowski pair of the two is a member two stages further up
-- (src/L/Axioms/Basic.lagda.md:596-599).  THREE STAGES ABOVE ITS OWN
-- INDEX, and that is where Devlin's four comes from: the sequence at
-- δ ≤ γ has its largest entry at γ, hence inside `Lset (step 3 γ)`,
-- hence the sequence itself one stage above that.
-- ===================================================================

Lset∈suc : (β : V ℓ) → ⟨ Lset β ∈ Lset (sucV β) ⟩
Lset∈suc β = subst (λ w → ⟨ Lset β ∈ w ⟩) (sym (Lset-suc β))
  (𝒟ₒ-intro (Lset β) (Lset β) ∣ ⊤̇ , DefOf.defSet⊤≡A (Lset β) ∣₁)

pr-at : (δ : V ℓ) → IsOrd δ → ⟨ pr δ (Lset δ) ∈ Lset (step 3 δ) ⟩
pr-at δ oδ = pr∈Lset-suc (sucV δ) δ (Lset δ) (ord∈Lset-suc δ oδ) (Lset∈suc δ)


-- ===================================================================
-- SECTION 5a.  THE REDUCTION.  StageHigh, from the sequence BELOW γ.
--
-- `HierBelow γ` says the internal hierarchy at γ itself, which records
-- the pairs at δ ∈ γ, is a member of `Lset (step 3 γ)`.  Given that,
-- the sequence at δ ≤ γ is that set with ONE pair adjoined, and the
-- adjunction is a two-constant definable subset of the same stage:
--
--     φ(z)  :=  z ∈ ḣ  ∨  z ≐ q̇
--
-- with `ḣ` the hierarchy below γ and `q̇` the pair at γ.  Both constants
-- are members of `Lset (step 3 γ)`: `q̇` by section 4, `ḣ` by the
-- hypothesis.  Nothing here is a quantifier, so the formula is the
-- cheapest shape the door admits.
--
-- THIS IS THE SUCCESSOR STEP OF THE INDUCTION AS WELL AS THE
-- REDUCTION, because `HierBelow (sucV α)` IS `StageHigh` at α.
-- ===================================================================

HierBelow : (γ : V ℓ) → IsOrd γ → Type (ℓ-suc ℓ)
HierBelow γ oγ = ⟨ fst (hierL γ (isL-ord γ oγ) oγ) ∈ Lset (step 3 γ) ⟩


-- ===================================================================
-- THE WALL, FACTORED.  runs/full-2 exhausted 8 GB and runs/full-3 is
-- the same file with ONE row removed, green at 11.13 s.  That row asked
-- Agda for a conversion and nothing else:
--
--     successor-step : (α : V ℓ) (oα : IsOrd α) → HierBelow α oα
--                    → HierBelow (sucV α) (suc-ord oα)
--     successor-step α oα h = Adjoin.seq∈ α oα h
--
-- This file measures the two factors of that conversion SEPARATELY.
-- Neither is the walling row and both are written as `p` alone, so a
-- green run here says the factors are free.
-- ===================================================================

-- FACTOR 1.  the step arithmetic: three successors above a successor
-- are four successors.  No hierarchy anywhere.
step-conv : (α x : V ℓ) → ⟨ x ∈ Lset (step 4 α) ⟩ → ⟨ x ∈ Lset (step 3 (sucV α)) ⟩
step-conv α x p = p

-- FACTOR 2.  the sequence identity: [LJ-1.519]'s `seq` at α IS the
-- internal hierarchy at sucV α.  No step arithmetic anywhere.
seq-conv : (α : V ℓ) (oα : IsOrd α) (x : V ℓ)
         → ⟨ x ∈ fst (seq α oα) ⟩
         → ⟨ x ∈ fst (hierL (sucV α) (isL-ord (sucV α) (suc-ord oα))
                             (suc-ord oα)) ⟩
seq-conv α oα x p = p

-- FACTOR 3.  the target type alone, formed and not inhabited.
target-only : (α : V ℓ) (oα : IsOrd α) → Type (ℓ-suc ℓ)
target-only α oα = HierBelow (sucV α) (suc-ord oα)

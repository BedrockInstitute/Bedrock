{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.565] CONTROL a.  THE CURE FOR [LJ-1.536]'S WALL, MEASURED
-- AGAINST THAT TASK'S OWN CONTROL.
--
-- This file is agents/tasks/LJ-1-536/runs/Control536e.agda with ONE
-- change: the body of `step-conv`.  That task's body is the variable
-- `p`, which asks Agda to convert `sucV` applied four times against
-- `sucV` applied three times to a successor.  `sucV` is transparent
-- (Cubical.HITs.CumulativeHierarchy.Constructions:156-157, :160-161),
-- so that is eight set layers normalized twice: 425.73 s
-- (agents/tasks/LJ-1-536/runs/ctle-0.time).
--
-- THE CURE IS TO PROVE THE IDENTITY AT A VARIABLE `n`.  With `n` a
-- variable `step` cannot unfold, so `sucV` is never unfolded either,
-- and every row matches syntactically.  Only then is it instantiated.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber.

open import Base.Prelude
open import Base.Truth

module LJ-1-565.runs.Control565a {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; Lset )

open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

step : ℕ → V ℓ → V ℓ
step zero    γ = γ
step (suc n) γ = sucV (step n γ)

-- THE CURE.  `n` is a variable throughout, so `step` is stuck at every
-- row and `sucV` is never unfolded.  The base case is `refl` between
-- two spellings that are ALREADY the same term (`sucV α` both sides),
-- and the step is `cong sucV` on the induction hypothesis, which never
-- looks inside its argument.
step-suc : (n : ℕ) (α : V ℓ) → step n (sucV α) ≡ sucV (step n α)
step-suc zero    α = refl
step-suc (suc n) α = cong sucV (step-suc n α)

-- THE SAME ROW [LJ-1.536] MEASURED, WITH THE CURE IN THE BODY.
step-conv : (α x : V ℓ) → ⟨ x ∈ Lset (step 4 α) ⟩ → ⟨ x ∈ Lset (step 3 (sucV α)) ⟩
step-conv α x p = subst (λ w → ⟨ x ∈ Lset w ⟩) (sym (step-suc 3 α)) p

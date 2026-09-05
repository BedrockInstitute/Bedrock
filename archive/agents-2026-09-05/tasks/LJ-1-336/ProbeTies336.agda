{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.336] TIE PROBE.  THE SECOND DIRTY MODULE'S TELESCOPE, SUPPLIED AT
-- THE AMBIENT CARRIER, AGAINST `[LJ-1.302]`'s ONE-DEBT CLAIM.
--
-- `[LJ-1.302]` supplied `DomainAgree`'s two ties at the ambient carrier in
-- 51 non-blank lines and then wrote:「The ties are ONE debt, not sixteen」
-- (agents/tasks/LJ-1-302/lj-1.302-report.md:191).  Its price for the whole
-- dirty seven, about 100 lines, rests on that claim: about 20 of shared
-- closure block written ONCE, then about 10 per module.
--
-- P-l says a judgement at one site is a hypothesis at another.  This file
-- measures the SECOND site.  It imports `[LJ-1.302]`'s own supply module
-- unchanged, so every line of its shared closure block is available for
-- free, and then supplies `EnvOneAgree`'s three ties at the same kind of
-- ambient environment.  What the second module needs BEYOND the first
-- module's block is the number the claim is about.
--
-- ONE agda process under GHCRTS="-A64m -I0 -M8g".

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

open import FOL.ZFStructure using ( module hPropStructure; Transitive; _↾_ )
open import FOL.Syntax using ( Formula; var; con; _≐_; _∧̇_; ∃̇_ )
import FOL.Absoluteness
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆; ∅ ) renaming ( module InfinitySet to Inf )
open Inf using ( #_; sucV )
open import Cubical.Data.Unit using ( tt* )

import LJ-1-336.GenDirty

module LJ-1-336.ProbeTies336 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( Lset; IsOrd )
open import L.Coding.Bound {ℓ} lem using ( module Bound )

import LJ-1-184.ProbeLJ1184A {ℓ} as P184
import LJ-1-297.ProbeLJ1297A {ℓ} lem as P1297A
import LJ-1-297.ProbeLJ1297C {ℓ} as P1297C
import LJ-1-302.ProbeLJ1302B {ℓ} lem as P1302B

module A = P184.Ambient
open P1297C using ( absFull )

-- The ambient class supplies all eight parameters, in `[LJ-1.302]`'s shape.
module GD = LJ-1-336.GenDirty {ℓ} P1297A.Full
  (λ {x} {y} → P1297A.Full-tr {x} {y})
  (λ k → # k , tt*) (λ k → refl)
  (λ a b → ⁅ fst a , fst b ⁆ , tt*) (λ a b → refl)
  (λ a → sucV (fst a) , tt*) (λ a → refl)

module AbsF = FOL.Absoluteness.Single 𝒮ᵥ P1297A.Full
  (λ {x} {y} → P1297A.Full-tr {x} {y})
open AbsF using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

toAmb : ∀ {n} (φ : Formula A.R.SC n) (γ : A.R.SC ^ n)
      → ⟨ γ ⊨ φ ⟩ → ⟨ A.ambient γ φ ⟩
toAmb φ γ = subst ⟨_⟩ (absFull φ γ)

fromAmb : ∀ {n} (φ : Formula A.R.SC n) (γ : A.R.SC ^ n)
        → ⟨ A.ambient γ φ ⟩ → ⟨ γ ⊨ φ ⟩
fromAmb φ γ = subst ⟨_⟩ (sym (absFull φ γ))

-- =====================================================================
-- PART 1.  WHAT `[LJ-1.302]`'s SHARED BLOCK GIVES THE SECOND MODULE.
-- The whole block arrives by import, unchanged, at zero new lines.
-- =====================================================================
module FirstBlock (lam beta gam : V ℓ)
                  (beta∈λ : ⟨ beta ∈ lam ⟩) (gam∈λ : ⟨ gam ∈ lam ⟩) where

  module S1 = P1302B.Supply lam beta gam beta∈λ gam∈λ

  -- The four names the first module's block holds, re-exported here so the
  -- reuse is visible rather than asserted.
  Ltr     = S1.Ltr
  x∈pair  = S1.x∈pair
  y∈pair  = S1.y∈pair
  pair∈pr = S1.pair∈pr

-- =====================================================================
-- PART 2.  `EnvOneAgree`'s THREE TIES, AT THE AMBIENT CARRIER.
--
-- `m := 3`, so `v := zero`, `K := suc zero`, `N0 := suc (suc zero)` and the
-- environment is five deep: two extension slots, then the three named ones.
-- The bound is `Lset lam` for a limit `lam`, the same bound the first
-- module used.
-- =====================================================================
module SecondModule (lam : V ℓ) (ordλ : IsOrd lam)
                    (succλ : (d : V ℓ) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩)
                    (∅∈λ : ⟨ ∅ ∈ lam ⟩)
                    (e0 e1 : A.R.SC) (e1∈ : ⟨ fst e1 ∈ Lset lam ⟩) where

  -- THE NEW CLOSURE BLOCK.  The first module's block proves DOWNWARD facts:
  -- a member of a member lands in the bound.  `pairK` is an UPWARD fact: a
  -- pair BUILT over the bound lands in the bound.  Nothing in the first
  -- block states it, so `L.Coding.Bound` enters here, with three
  -- hypotheses the first module never needed.
  module B = Bound lam ordλ succλ ∅∈λ

  vval Kval N0val : A.R.SC
  vval  = Lset lam , tt*
  Kval  = Lset lam , tt*
  N0val = # 0 , tt*

  env : A.R.SC ^ 5
  env = e0 ∷ e1 ∷ vval ∷ Kval ∷ N0val ∷ []

  -- TIE 1.  `N0eq`: the numeral slot holds the numeral.
  N0eq : fst (lookup (suc (suc (suc (suc zero)))) env) ≡ # 0
  N0eq = refl

  -- TIE 2.  `numK`: the numeral lands in the bound.  UPWARD, and the first
  -- module's block does not have it.
  numK : ⟨ # 0 ∈ fst (lookup (suc (suc (suc zero))) env) ⟩
  numK = B.#∈Tλ 0

  -- TIE 3.  `pairK`: the tagged pair lands in the bound.  UPWARD again, and
  -- it needs the tag reading first.
  pairK : (z : A.R.SC)
        → ⟨ (z ∷ env) ⊨ GD.W1.GM.tagAtL zero 0 (suc (suc zero)) ⟩
        → ⟨ fst z ∈ fst (lookup (suc (suc (suc zero))) env) ⟩
  pairK z h = subst (λ w → ⟨ w ∈ Lset lam ⟩)
    (sym (subst ⟨_⟩ (GD.W1.GM.tagAtL-adequate zero 0 (suc (suc zero)) (z ∷ env)) h))
    (B.pr∈λ (# 0) (fst e1) (B.#∈Tλ 0) e1∈)

  -- THE SECOND DIRTY MODULE, INSTANTIATED WITH ALL THREE TIES SUPPLIED.
  module EO = GD.EnvOneAgree {3} zero (suc zero) (suc (suc zero))
                env N0eq numK pairK

  out-amb : ⟨ A.ambient env (GD.envOneAt zero (suc zero)) ⟩
          → ⟨ A.ambient env (GD.envOneBndS zero (suc zero) (suc (suc zero))) ⟩
  out-amb h = toAmb (GD.envOneBndS zero (suc zero) (suc (suc zero))) env
    (EO.out (fromAmb (GD.envOneAt zero (suc zero)) env h))

  back-amb : ⟨ A.ambient env (GD.envOneBndS zero (suc zero) (suc (suc zero))) ⟩
           → ⟨ A.ambient env (GD.envOneAt zero (suc zero)) ⟩
  back-amb h = toAmb (GD.envOneAt zero (suc zero)) env
    (EO.back (fromAmb (GD.envOneBndS zero (suc zero) (suc (suc zero))) env h))

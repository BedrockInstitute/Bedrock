{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.293] probe A.  THE MACHINE-CHECKED REFUTATION OF `q`.
--
-- `q` is `Graph {2} zero (suc zero) ≡ embed φ₀`
-- (agents/tasks/LJ-1-184/ProbeLJ1184B.agda:112), and nothing
-- instantiates its module (only the relay at ProbeLJ1184C.agda:83).
-- The intended instantiation is `Graph := LsetGraphAt`, the ambient
-- port of the delivered `L.Coding.Sequence` coding, as the probe's own
-- residue statement names it (ProbeLJ1184B.agda:48-51).
--
-- [LJ-1.242] measured the equation false at that instantiation by
-- READING two constructor chains, and [LJ-1.243] upheld the reading but
-- re-ran nothing.  This probe turns the reading into a term:
--
--   LHS  `LsetGraphAt {2} zero (suc zero)`
--        = `∃̇ (ApproxAt zero (suc (suc zero)) ∧̇ StepAt ...)`, ONE `∃̇`
--        over a `∧̇` (GenSequence.agda:167);
--   RHS  `embed φ₀` = fourteen nested `∃̇` over one `∧̇`
--        (`closeN 14 (pins ∧̇ renamed)`, ProbeLJ1241A.agda:145-146).
--
-- The two formulas differ at depth two: `∧̇` against `∃̇`, two
-- constructors of one data type (src/FOL/Syntax.lagda.md:96,99).  So no
-- path connects the two sides, and `q` implies Empty.
--
-- The Def-step coding enters as THREE HYPOTHESES, so the refutation
-- holds for EVERY `DefAt`: the depth-two shape of `LsetGraphAt` does
-- not depend on it.  C-36 answered: the term that could not be written
-- is `q` itself, and here is the proof that it cannot be.
--
-- ONE agda process under GHCRTS="-A64m -I0 -M8g".

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-293.ProbeLJ1293A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure; Transitive; _↾_ )
open import FOL.Syntax using ( Formula; _∧̇_; ∃̇_ )
open import FOL.Manipulation.Relabelling using ( embed )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒟ₒ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆ ) renaming ( module InfinitySet to Inf )
open Inf using ( #_; sucV )
open import Cubical.Data.Unit using ( Unit*; tt*; isPropUnit* )
import Cubical.Data.Empty as Empty
import LJ-1-238.GenSequence
import LJ-1-241.ProbeLJ1241A
import LJ-1-184.ProbeLJ1184A as P184

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))

-- The ambient class, [LJ-1.184] probe A section 4's `Full`, at the type
-- GenSequence's telescope writes for `M`.
Full : V ℓ → hProp (ℓ-suc ℓ)
Full _ = Unit* {ℓ-suc ℓ} , isPropUnit*

Full-tr : Transitive 𝒮ᵥ Full
Full-tr h k = tt*

module GS = LJ-1-238.GenSequence {ℓ} lem Full
  (λ {x} {y} → Full-tr {x} {y})
  (λ k → # k , tt*) (λ k → refl)
  (λ a b → ⁅ fst a , fst b ⁆ , tt*) (λ a b → refl)
  (λ a → sucV (fst a) , tt*) (λ a → refl)

open hPropStructure (𝒮ᵥ ↾ Full)

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ Full
  (λ {x} {y} → Full-tr {x} {y})
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

module P1241 = LJ-1-241.ProbeLJ1241A {ℓ} lem

-- THE CARRIER CHECK.  The port's carrier IS probe A's ambient carrier,
-- by `refl`, so the equation refuted below is `q` at the intended
-- reading (`Graph := LsetGraphAt`).
ambient≡ : S ≡ P184.Ambient.R.SC
ambient≡ = refl

-- =====================================================================
-- THE DISCRIMINATOR.  The formula's constructor at depth two, tagged.
-- =====================================================================

data Tag : Type (ℓ-suc ℓ) where
  isEx isAnd neither : Tag

tag₁ : ∀ {K : Type (ℓ-suc ℓ)} {n} → Formula K n → Tag
tag₁ (∃̇ _)   = isEx
tag₁ (φ ∧̇ ψ) = isAnd
tag₁ _        = neither

tag₂ : ∀ {K : Type (ℓ-suc ℓ)} {n} → Formula K n → Tag
tag₂ (∃̇ φ) = tag₁ φ
tag₂ _     = neither

-- =====================================================================
-- THE REFUTATION.  The DefAt trio enters as hypotheses (the readings
-- are never spent), so the term holds for every Def-step coding.
-- =====================================================================

module RefuteQ
  (DefAt : ∀ {n} → Fin n → Fin n → Formula S n)
  (DefAt-in : (A : S) → ∀ {n} (u w : Fin n) (γ : S ^ n)
            → fst (lookup w γ) ≡ fst A
            → fst (lookup u γ) ≡ 𝒟ₒ (fst A)
            → ⟨ γ ⊨ DefAt u w ⟩)
  (DefAt-out : (A : S) → ∀ {n} (u w : Fin n) (γ : S ^ n) → GS.DefOK A
             → fst (lookup w γ) ≡ fst A
             → ⟨ γ ⊨ DefAt u w ⟩
             → fst (lookup u γ) ≡ 𝒟ₒ (fst A))
  where

  module Seq = GS.Body DefAt DefAt-in DefAt-out

  -- `q` at the intended instantiation.
  IntendedQ : Type (ℓ-suc ℓ)
  IntendedQ = Seq.LsetGraphAt {2} zero (suc zero) ≡ embed P1241.φ₀

  -- THE MEASUREMENT, both sides by `refl`.
  left-tag : tag₂ (Seq.LsetGraphAt {2} zero (suc zero)) ≡ isAnd
  left-tag = refl

  right-tag : tag₂ {K = S} (embed P1241.φ₀) ≡ isEx
  right-tag = refl

  -- THE REFUTATION TERM.
  q-false : IntendedQ → Empty.⊥
  q-false h = lower (subst (λ ψ → Case (tag₂ ψ)) h tt*)
    where
    Case : Tag → Type (ℓ-suc ℓ)
    Case isEx = Lift Empty.⊥
    Case _    = Unit*

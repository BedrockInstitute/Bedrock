{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.302] probe, file 2 of the pricing.  THE DIRTY MODULE'S
-- TELESCOPE, SUPPLIED AT THE AMBIENT CARRIER.
--
-- `GenDomainAgree.agda` ports `DomainAgree` (one of the dirty seven)
-- with the class as a parameter.  This file applies it at the AMBIENT
-- class `Full`, in the shape `[LJ-1.298]`'s `ProbeLJ1298Amb` used, and
-- then SUPPLIES the module's two site ties (`entryK`, `domK`) at a
-- concrete ambient environment, the way `[LJ-1.297]`'s probe D supplied
-- `AmbientStep`'s six readings from delivered machinery.
--
-- The supply site: `f := Lset beta`, `d := Lset gam`, `K := Lset lam`,
-- with `beta`, `gam` members of `lam`.  Every ingredient is delivered:
-- `pairing-ax` (pairs), `layer-trans`/`Lset-layer` (`Lset beta` is
-- transitive), `Lset-mono` (`Lset gam` sits inside `Lset lam`).  NO
-- new mathematics is written: the measurement is the plumbing cost.
--
-- ONE agda process under GHCRTS="-A64m -I0 -M8g".

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

open import FOL.ZFStructure using ( module hPropStructure; Transitive; _↾_ )
open import FOL.Syntax using ( Formula )
import FOL.Absoluteness
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ∈∈ₛ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆; ⁅_⁆s; pairing-ax ) renaming ( module InfinitySet to Inf )
open Inf using ( #_; sucV )
open import Cubical.Data.Unit using ( tt* )
open import Cubical.Data.Sum using ( inl; inr )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )

import LJ-1-302.GenDomainAgree

module LJ-1-302.ProbeLJ1302B {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ}
  using ( Lset; Lset-mono; layer-trans; Lset-layer )

import LJ-1-184.ProbeLJ1184A {ℓ} as P184
import LJ-1-297.ProbeLJ1297A {ℓ} lem as P1297A
import LJ-1-297.ProbeLJ1297C {ℓ} as P1297C

module A = P184.Ambient
open P1297C using ( absFull )

-- The ambient class supplies all eight parameters, in the shape probe D
-- used for `GenSequence` and probe `[LJ-1.298]` used for `GenTagAgree`.
module GDA = LJ-1-302.GenDomainAgree {ℓ} P1297A.Full
  (λ {x} {y} → P1297A.Full-tr {x} {y})
  (λ k → # k , tt*) (λ k → refl)
  (λ a b → ⁅ fst a , fst b ⁆ , tt*) (λ a b → refl)
  (λ a → sucV (fst a) , tt*) (λ a → refl)

-- The reading the generic module carries, at the ambient class, and the
-- transport to the ambient reading, both cribbed from `ProbeLJ1298Amb`.
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
-- THE SUPPLY.  Two ties, at a concrete ambient environment.  The
-- environment is the three-slot frame `f ∷ d ∷ K ∷ []` with every
-- value a stage below the bound `Lset lam`.
-- =====================================================================
module Supply (lam beta gam : V ℓ)
              (beta∈λ : ⟨ beta ∈ lam ⟩) (gam∈λ : ⟨ gam ∈ lam ⟩) where

  fval dval Kval : A.R.SC
  fval = Lset beta , tt*
  dval = Lset gam , tt*
  Kval = Lset lam , tt*

  env : A.R.SC ^ 3
  env = fval ∷ dval ∷ Kval ∷ []

  -- `Lset beta` is transitive, delivered.
  Ltr = layer-trans (Lset-layer beta)

  -- The pair-component memberships, from the pairing axiom, moved from
  -- the `∈ₛ` statement to `∈` by `∈∈ₛ`.
  x∈pair : (x y : V ℓ) → ⟨ x ∈ ⁅ x , y ⁆ ⟩
  x∈pair x y =
    ∈∈ₛ {a = x} {b = ⁅ x , y ⁆} .snd (pairing-ax x y x .snd ∣ inl refl ∣₁)

  y∈pair : (x y : V ℓ) → ⟨ y ∈ ⁅ x , y ⁆ ⟩
  y∈pair x y =
    ∈∈ₛ {a = y} {b = ⁅ x , y ⁆} .snd (pairing-ax x y y .snd ∣ inr refl ∣₁)

  pair∈pr : (x y : V ℓ) → ⟨ ⁅ x , y ⁆ ∈ pr x y ⟩
  pair∈pr x y =
    ∈∈ₛ {a = ⁅ x , y ⁆} {b = pr x y} .snd
      (pairing-ax ⁅ x ⁆s ⁅ x , y ⁆ (⁅ x , y ⁆) .snd ∣ inr refl ∣₁)

  -- TIE 1.  `entryK`: the pair components of `f`'s members land in `K`.
  -- Two transitivity steps through the Kuratowski pair, then the stage
  -- monotonicity.
  entryK : (x y : A.R.SC) → ⟨ pr (fst x) (fst y) ∈ fst (lookup zero env) ⟩
         → ⟨ fst x ∈ fst (lookup (suc (suc zero)) env) ⟩
           × ⟨ fst y ∈ fst (lookup (suc (suc zero)) env) ⟩
  entryK x y h =
    ( Lset-mono {α = lam} {β = beta} beta∈λ
        (Ltr (x∈pair (fst x) (fst y))
          (Ltr (pair∈pr (fst x) (fst y)) h))
    , Lset-mono {α = lam} {β = beta} beta∈λ
        (Ltr (y∈pair (fst x) (fst y))
          (Ltr (pair∈pr (fst x) (fst y)) h)) )

  -- TIE 2.  `domK`: `d` sits inside `K`, by stage monotonicity alone.
  domK : (x : A.R.SC) → ⟨ fst x ∈ fst (lookup (suc zero) env) ⟩
       → ⟨ fst x ∈ fst (lookup (suc (suc zero)) env) ⟩
  domK x hx = Lset-mono {α = lam} {β = gam} gam∈λ hx

  -- THE DIRTY MODULE, INSTANTIATED AT THE AMBIENT CARRIER WITH BOTH
  -- TIES SUPPLIED.  `out` and `back` are then TERMS at the ambient
  -- carrier, not hypotheses.
  module DA = GDA.DomainAgree zero (suc zero) (suc (suc zero)) env entryK domK

  out-amb : ⟨ A.ambient env (GDA.GM.domAt zero (suc zero)) ⟩
          → ⟨ A.ambient env (GDA.domB zero (suc zero) (suc (suc zero))) ⟩
  out-amb h = toAmb (GDA.domB zero (suc zero) (suc (suc zero))) env
    (DA.out (fromAmb (GDA.GM.domAt zero (suc zero)) env h))

  back-amb : ⟨ A.ambient env (GDA.domB zero (suc zero) (suc (suc zero))) ⟩
           → ⟨ A.ambient env (GDA.GM.domAt zero (suc zero)) ⟩
  back-amb h = toAmb (GDA.GM.domAt zero (suc zero)) env
    (DA.back (fromAmb (GDA.domB zero (suc zero) (suc (suc zero))) env h))

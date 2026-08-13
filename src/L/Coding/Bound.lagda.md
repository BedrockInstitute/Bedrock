# The bound at a limit

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Coding.Bound {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; IsOrd; Lset; 𝒟ₒ; Lset-out; Lset-mono; layer-trans; Lset-layer )
open import L.Axioms.Basic {ℓ} using ( Lset-suc; pr∈Lset-suc )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )
open import L.Ordinal {ℓ} using ( mem-ord; suc-ord; numeral-ord )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.Ordinal.StageArith {ℓ} lem using ( sucIter )
open import L.Coding.Model {ℓ} using ( prʟ; prʟ-fst )

import Cubical.Data.Sum as Sum
open import Cubical.Data.Sigma using ( _×_; _,_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; module InfinitySet )
open InfinitySet using ( #_; sucV )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

module CS = hPropStructure 𝒮ʟ

-- A stage function and the five facts the closure argument uses.  Nothing in
-- this module names a tower: the argument is decompose, merge two stages by
-- trichotomy, climb by one successor, and every tower supplies that shape.
module BoundOver
  (T : S → S)
  (T-out : (α x : S) → ⟨ x ∈ˢ T α ⟩
         → ∥ Σ[ δ ∈ S ] (⟨ δ ∈ˢ α ⟩ × ⟨ x ∈ˢ T (sucV δ) ⟩) ∥₁)
  (T-mono : {α β : S} → ⟨ β ∈ˢ α ⟩ → {x : S} → ⟨ x ∈ˢ T β ⟩ → ⟨ x ∈ˢ T α ⟩)
  (T-pr : (σ x y : S) → ⟨ x ∈ˢ T σ ⟩ → ⟨ y ∈ˢ T σ ⟩
        → ⟨ pr x y ∈ˢ T (sucV (sucV σ)) ⟩)
  (T-trans : (α : S) {x y : S} → ⟨ y ∈ˢ x ⟩ → ⟨ x ∈ˢ T α ⟩ → ⟨ y ∈ˢ T α ⟩)
  (T-ord : (δ : S) → IsOrd δ → ⟨ δ ∈ˢ T (sucV δ) ⟩)
  (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  -- Every numeral is an ordinal of the limit, by the two parameters alone.
  #∈λ : (k : ℕ) → ⟨ (# k) ∈ˢ lam ⟩
  #∈λ zero    = ∅∈λ
  #∈λ (suc k) = succλ (# k) (#∈λ k)

  -- The formula set: Devlin's `𝓕 ∪ {vᵢ}`, here the numerals.
  #∈Tλ : (k : ℕ) → ⟨ (# k) ∈ˢ T lam ⟩
  #∈Tλ k = T-mono {α = lam} {β = sucV (# k)} (#∈λ (suc k))
    {x = # k} (T-ord (# k) (numeral-ord k))

  At : S → Type (ℓ-suc ℓ)
  At x = Σ[ δ ∈ S ] (⟨ δ ∈ˢ lam ⟩ × ⟨ x ∈ˢ T (sucV δ) ⟩)

  -- The sequences: the Kuratowski pair, which every code is built from.  This
  -- is the one `κ → κ` pairing closure, at an ARBITRARY limit.
  pr∈λ : (x y : S) → ⟨ x ∈ˢ T lam ⟩ → ⟨ y ∈ˢ T lam ⟩ → ⟨ pr x y ∈ˢ T lam ⟩
  pr∈λ x y hx hy = PT.rec (snd (pr x y ∈ˢ T lam))
    (λ px → PT.rec (snd (pr x y ∈ˢ T lam)) (both px) (T-out lam y hy))
    (T-out lam x hx)
    where
    climb : (σ : S) → ⟨ σ ∈ˢ lam ⟩ → ⟨ x ∈ˢ T σ ⟩ → ⟨ y ∈ˢ T σ ⟩
          → ⟨ pr x y ∈ˢ T lam ⟩
    climb σ σ∈ hxσ hyσ =
      T-mono {α = lam} {β = sucV (sucV σ)}
        (succλ (sucV σ) (succλ σ σ∈)) {x = pr x y} (T-pr σ x y hxσ hyσ)
    both : At x → At y → ⟨ pr x y ∈ˢ T lam ⟩
    both (δ , (δ∈ , hxδ)) (ε , (ε∈ , hyε)) =
      Sum.rec
        (λ p → climb (sucV ε) (succλ ε ε∈)
                 (T-mono {α = sucV ε} {β = sucV δ} p {x = x} hxδ) hyε)
        (Sum.rec
          (λ q → climb (sucV ε) (succλ ε ε∈)
                   (subst (λ w → ⟨ x ∈ˢ T w ⟩) q hxδ) hyε)
          (λ r → climb (sucV δ) (succλ δ δ∈) hxδ
                   (T-mono {α = sucV δ} {β = sucV ε} r {x = y} hyε)))
        (ord-tri (sucV δ) (suc-ord {A = δ} (mem-ord {A = lam} ordλ δ δ∈))
                 (sucV ε) (suc-ord {A = ε} (mem-ord {A = lam} ordλ ε ε∈)))

  -- The carrier and the transitivity, one call each.
  trans∈λ : {x y : S} → ⟨ y ∈ˢ x ⟩ → ⟨ x ∈ˢ T lam ⟩ → ⟨ y ∈ˢ T lam ⟩
  trans∈λ {x} {y} = T-trans lam {x = x} {y = y}

  -- Climbing any finite iterate costs `succλ` alone: no limit fact enters.
  suc^∈λ : (k : ℕ) (σ : S) → ⟨ σ ∈ˢ lam ⟩ → ⟨ sucIter k σ ∈ˢ lam ⟩
  suc^∈λ zero    σ h = h
  suc^∈λ (suc k) σ h = succλ (sucIter k σ) (suc^∈λ k σ h)

  -- The step operator at a limit, reduced to ONE fact about the step at a
  -- successor: the step of a stage member lands a bounded number of stages
  -- above it.  The fact is a HYPOTHESIS here and it has no supplier; `src/`
  -- assumes the same fact twice, as `DefOK` and as `PowOK`.
  module Iter (D : S → S)
    (powIter : (δ y : S) → ⟨ y ∈ˢ T δ ⟩
             → ∥ Σ[ k ∈ ℕ ] ⟨ D y ∈ˢ T (sucIter k δ) ⟩ ∥₁) where

    pow∈λ : (x : S) → ⟨ x ∈ˢ T lam ⟩ → ⟨ D x ∈ˢ T lam ⟩
    pow∈λ x hx = PT.rec (snd (D x ∈ˢ T lam)) step (T-out lam x hx)
      where
      step : At x → ⟨ D x ∈ˢ T lam ⟩
      step (δ , (δ∈ , hδ)) = PT.rec (snd (D x ∈ˢ T lam))
        (λ { (k , hk) → T-mono {α = lam} {β = sucIter k (sucV δ)}
               (suc^∈λ k (sucV δ) (succλ δ δ∈)) {x = D x} hk })
        (powIter (sucV δ) x hδ)

-- The L tower supplies the five facts.  Two need an adapter, and both
-- adapters are one call: `Lset-out` lands in `𝒟ₒ` and `Lset-suc` renames it.
Lset-out′ : (α x : S) → ⟨ x ∈ˢ Lset α ⟩
          → ∥ Σ[ δ ∈ S ] (⟨ δ ∈ˢ α ⟩ × ⟨ x ∈ˢ Lset (sucV δ) ⟩) ∥₁
Lset-out′ α x hx = PT.map
  (λ { (δ , (δ∈ , h)) → δ , (δ∈ , subst (λ w → ⟨ x ∈ˢ w ⟩)
         (sym (Lset-suc δ)) h) })
  (Lset-out α x hx)

Lset-trans′ : (α : S) {x y : S} → ⟨ y ∈ˢ x ⟩ → ⟨ x ∈ˢ Lset α ⟩ → ⟨ y ∈ˢ Lset α ⟩
Lset-trans′ α {x} {y} = layer-trans (Lset-layer α) {x = x} {y = y}

module Bound (lam : S) (ordλ : IsOrd lam)
             (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
             (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  open BoundOver Lset Lset-out′ Lset-mono pr∈Lset-suc Lset-trans′
    ord∈Lset-suc lam ordλ succλ ∅∈λ public

  -- The numerals as elements of L, and the model's own pair.  Both are the
  -- L presentation of a fact `BoundOver` already has.
  num∈λ : (k : ℕ) → ⟨ fst (numeralL k) ∈ˢ Lset lam ⟩
  num∈λ k = subst (λ w → ⟨ w ∈ˢ Lset lam ⟩) (sym (numeralL-fst k)) (#∈Tλ k)

  prʟ∈λ : (a b : CS.S) → ⟨ fst a ∈ˢ Lset lam ⟩ → ⟨ fst b ∈ˢ Lset lam ⟩
        → ⟨ fst (prʟ a b) ∈ˢ Lset lam ⟩
  prʟ∈λ a b ha hb = subst (λ w → ⟨ w ∈ˢ Lset lam ⟩) (sym (prʟ-fst a b))
    (pr∈λ (fst a) (fst b) ha hb)

  -- The reduction at the L step operator.  `powIter` stays a hypothesis:
  -- MEASURED, nothing in `src/` proves it, and `L.Coding.Powerset` and
  -- `L.Coding.Sequence` each assume it under another name.
  module PowIter
    (powIter : (δ y : S) → ⟨ y ∈ˢ Lset δ ⟩
             → ∥ Σ[ k ∈ ℕ ] ⟨ 𝒟ₒ y ∈ˢ Lset (sucIter k δ) ⟩ ∥₁) where
    open Iter 𝒟ₒ powIter public
```

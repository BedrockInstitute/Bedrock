# The C-45 consumer probe for [LJ-1.289]

C-45 says an `exit 0` is not a supply. This probe IMPORTS the landed master
and APPLIES the `sucK` field at its declared type. The respelling changes the
proof inside `sucK`, never the statement, so a consumer that reads the
interface must still see the same field.

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-289.Consume {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where
open import FOL.ZFStructure using ( module hPropStructure )
open import L.Constructible {ℓ} using ( 𝒮ʟ; Lset; IsOrd )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; module InfinitySet )
open InfinitySet using ( sucV; ω )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

open import L.Coding.EnvSupply {ℓ} lem using ( module SupplyEnv )

module _ (lam : V ℓ) (ordλ : IsOrd lam)
  (succλ : (d : V ℓ) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ lam ⟩)
  (gam : V ℓ) (ordγ : IsOrd gam) (γ∈λ : ⟨ gam ∈ lam ⟩)
  (ω∈γ : ⟨ ω ∈ sucV gam ⟩) where

  module SE = SupplyEnv lam ordλ succλ ∅∈λ gam ordγ γ∈λ ω∈γ

  -- The field, read from the interface and applied.
  useSucK : (a : V ℓ) → ⟨ a ∈ Lset lam ⟩ → ⟨ sucV a ∈ Lset lam ⟩
  useSucK = SE.sucK

  -- The same field, used at an argument, so the application elaborates.
  sucOfEmpty : ⟨ ∅ ∈ Lset lam ⟩ → ⟨ sucV ∅ ∈ Lset lam ⟩
  sucOfEmpty h = SE.sucK ∅ h
```

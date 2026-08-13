{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.85] probe C: RED, deliberately.  The adaptation of the LJ-1.84
-- refutation to the repaired statement cannot be typechecked.
--
-- The repaired witK adds the premise w ⊆ AllCodes A₀.  The old refutation
-- extends a closed shaped code set D by the junk member
--     c₀ = pr K₀ (pr (#6) (numeralL 0))
-- whose arity slot is the stage bound itself.  Supplying the new premise
-- for the extended witness w = D ∪ {c₀} needs c₀ ∈ AllCodes A₀, i.e. the
-- junk member must be the key of some formula over the carrier.  The
-- natural attempt below writes c₀ as the key of the constant truth at
-- arity zero; Agda rejects it, because the junk member's arity slot is
-- Lset lam, which is not the numeral # 0 (machine-checked green in
-- ProbeLJ185A: c₀∉All).  This file is expected to FAIL typechecking.
--
-- Untracked probe; one Agda process under GHCRTS="-A64m -I0 -M8g";
-- never committed.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ185C {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( ZFStructure; module hPropStructure )
open import FOL.Syntax using ( ⊤̇ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; IsOrd )
open import L.Coding.Model {ℓ} using ( prʟ )
open import L.Coding.CodeSet {ℓ} lem using ( AllCodes; key∈AllCodes )
open import L.Axioms.Numerals {ℓ} using ( numeralL )
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet using ( ω; #_ )
import Cubical.Data.Empty as Empty
open import Cubical.Data.Nat using ( zero )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

Sʟ : Type (ℓ-suc ℓ)
Sʟ = ZFStructure.S 𝒮ʟ

module Stage (lam : V ℓ) (ordλ : IsOrd lam)
  (α : V ℓ) (ordα : IsOrd α) (α∈λ : ⟨ α ∈ˢ lam ⟩)
  (α∉ω : ⟨ α ∈ˢ ω ⟩ → Empty.⊥) where

  K₀ : Sʟ
  K₀ = LsetS lam ordλ

  A₀ : Sʟ
  A₀ = LsetS α ordα

  c₀ : Sʟ
  c₀ = prʟ K₀ (prʟ (numeralL 6) (numeralL 0))

  -- THE MISSING PREMISE TERM.  The junk member is not the key of the
  -- constant truth at arity zero (nor of any formula over the carrier);
  -- the term below cannot be written and Agda rejects it.
  c₀∈All : ⟨ fst c₀ ∈ˢ fst (AllCodes A₀) ⟩
  c₀∈All = key∈AllCodes A₀ (⊤̇ {n = zero})

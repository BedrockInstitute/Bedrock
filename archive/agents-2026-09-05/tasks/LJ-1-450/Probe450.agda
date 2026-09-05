{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.450] W3 FIRST: do the 24 TFacts tagEq/numK fields transfer
-- from KValue.facts onto Kenv under TFacts's suc^6 convention?
-- Then the obligation someEnv-at-K : someEnvDef {3} iK Kenv.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber,
-- set on the pane by the program and untouched here.
-- Nothing lands in src/.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-450.Probe450 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd )
open import L.Axioms.Numerals {ℓ} using ( numeralL )
open import L.Condensation {ℓ} lem using ( module KValue; module KFactsNS )
open import L.Condensation.LowerAgree {ℓ} lem using ( someEnvDef )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; ∅ )
open InfinitySet using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ
open KFactsNS

-- =====================================================================
-- W3.  The 24 TFacts tagEq/numK fields (TwelveAgree.lagda.md:133-156)
-- as a record at KValue's Kenv, inhabited from KValue.facts.
-- TFacts {3} wants Fin 8.  KValue delivers Fin 14.  Obligation omitted.
-- =====================================================================

module W3
  (lam : V ℓ) (ordλ : IsOrd lam)
  (succλ : (d : V ℓ) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ lam ⟩)
  (gam : V ℓ) (ordγ : IsOrd gam) (γ∈λ : ⟨ gam ∈ lam ⟩) where

  open KValue lam ordλ succλ ∅∈λ gam ordγ γ∈λ

  -- THE OBLIGATION, as the brief names it.  someEnvDef {3} wants
  -- K : Fin 8.  iK : Fin 14.  W3 below is the 24-field layout check.
  someEnv-at-K : someEnvDef {3} iK Kenv
  someEnv-at-K = {!!}

  -- n = 3 so |γ'| = 11 + 3 = 14 = |Kenv|.  Indices are Fin (5 + 3) = Fin 8.
  -- Lookups are TFacts's suc^6 (TwelveAgree.lagda.md:133-156).
  record TagNum (N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 K : Fin 8)
                : Type (ℓ-suc ℓ) where
    field
      tagEq0 : fst (lookup (suc (suc (suc (suc (suc (suc N0)))))) Kenv) ≡ fst (numeralL 0)
      tagEq1 : fst (lookup (suc (suc (suc (suc (suc (suc N1)))))) Kenv) ≡ fst (numeralL 1)
      tagEq2 : fst (lookup (suc (suc (suc (suc (suc (suc N2)))))) Kenv) ≡ fst (numeralL 2)
      tagEq3 : fst (lookup (suc (suc (suc (suc (suc (suc N3)))))) Kenv) ≡ fst (numeralL 3)
      tagEq4 : fst (lookup (suc (suc (suc (suc (suc (suc N4)))))) Kenv) ≡ fst (numeralL 4)
      tagEq5 : fst (lookup (suc (suc (suc (suc (suc (suc N5)))))) Kenv) ≡ fst (numeralL 5)
      tagEq6 : fst (lookup (suc (suc (suc (suc (suc (suc N6)))))) Kenv) ≡ fst (numeralL 6)
      tagEq7 : fst (lookup (suc (suc (suc (suc (suc (suc N7)))))) Kenv) ≡ fst (numeralL 7)
      tagEq8 : fst (lookup (suc (suc (suc (suc (suc (suc N8)))))) Kenv) ≡ fst (numeralL 8)
      tagEq9 : fst (lookup (suc (suc (suc (suc (suc (suc N9)))))) Kenv) ≡ fst (numeralL 9)
      tagEq10 : fst (lookup (suc (suc (suc (suc (suc (suc N10)))))) Kenv) ≡ fst (numeralL 10)
      tagEq11 : fst (lookup (suc (suc (suc (suc (suc (suc N11)))))) Kenv) ≡ fst (numeralL 11)
      numK0 : ⟨ fst (numeralL 0) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) Kenv) ⟩
      numK1 : ⟨ fst (numeralL 1) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) Kenv) ⟩
      numK2 : ⟨ fst (numeralL 2) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) Kenv) ⟩
      numK3 : ⟨ fst (numeralL 3) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) Kenv) ⟩
      numK4 : ⟨ fst (numeralL 4) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) Kenv) ⟩
      numK5 : ⟨ fst (numeralL 5) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) Kenv) ⟩
      numK6 : ⟨ fst (numeralL 6) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) Kenv) ⟩
      numK7 : ⟨ fst (numeralL 7) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) Kenv) ⟩
      numK8 : ⟨ fst (numeralL 8) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) Kenv) ⟩
      numK9 : ⟨ fst (numeralL 9) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) Kenv) ⟩
      numK10 : ⟨ fst (numeralL 10) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) Kenv) ⟩
      numK11 : ⟨ fst (numeralL 11) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) Kenv) ⟩

  -- The 24 fields at Kenv, inhabited from facts.  TFacts indices are Fin 8.
  -- Generic Fin 8 still fails: suc^6 N0 != i0.
  -- Sibling IndexCheck asks whether iK : Fin 14 can be a TFacts {3} slot.
  module Transfer
    (N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 K : Fin 8) where

    frame-sigma : TagNum N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 K
    frame-sigma = record
      { tagEq0 = KFacts.tagEq0 facts
      ; tagEq1 = KFacts.tagEq1 facts
      ; tagEq2 = KFacts.tagEq2 facts
      ; tagEq3 = KFacts.tagEq3 facts
      ; tagEq4 = KFacts.tagEq4 facts
      ; tagEq5 = KFacts.tagEq5 facts
      ; tagEq6 = KFacts.tagEq6 facts
      ; tagEq7 = KFacts.tagEq7 facts
      ; tagEq8 = KFacts.tagEq8 facts
      ; tagEq9 = KFacts.tagEq9 facts
      ; tagEq10 = KFacts.tagEq10 facts
      ; tagEq11 = KFacts.tagEq11 facts
      ; numK0 = KFacts.numK0 facts
      ; numK1 = KFacts.numK1 facts
      ; numK2 = KFacts.numK2 facts
      ; numK3 = KFacts.numK3 facts
      ; numK4 = KFacts.numK4 facts
      ; numK5 = KFacts.numK5 facts
      ; numK6 = KFacts.numK6 facts
      ; numK7 = KFacts.numK7 facts
      ; numK8 = KFacts.numK8 facts
      ; numK9 = KFacts.numK9 facts
      ; numK10 = KFacts.numK10 facts
      ; numK11 = KFacts.numK11 facts }

  -- Can KValue's iK inhabit TFacts {3}'s K slot?  iK : Fin 14, want Fin 8.
  module IndexCheck where
    k-as-TFacts : Fin 8
    k-as-TFacts = iK

{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.534] BISECTION 1.  The record ALONE.  No frame, no witness.
-- Runs 0 and 1 both walled at 8 GB; the record is the part they share.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-534.runs.R {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isTransV )
open import L.Axioms.Basic {ℓ} using ( finSet )
open import L.Coding.EnvSet {ℓ} lem using ( module Generic )
open import Cubical.Data.Nat using ( ℕ; _+_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( #_; sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

Kslot : {n : ℕ} → Fin (5 + n) → Vec S (11 + n) → S
Kslot K γ = lookup (suc (suc (suc (suc (suc (suc K)))))) γ

record HonestFrame {n : ℕ} (A K : Fin (5 + n)) (γ : Vec S (11 + n))
  : Type (ℓ-suc ℓ) where
  field
    Ktr : isTransV (fst (Kslot K γ))
    TK : ⟨ fst (lookup (suc zero) γ) ∈ fst (Kslot K γ) ⟩
    numK0 : ⟨ # 0 ∈ fst (Kslot K γ) ⟩
    sucK : (a : V ℓ) → ⟨ a ∈ fst (Kslot K γ) ⟩
         → ⟨ sucV a ∈ fst (Kslot K γ) ⟩
    pairK : (a b : V ℓ) → ⟨ a ∈ fst (Kslot K γ) ⟩ → ⟨ b ∈ fst (Kslot K γ) ⟩
          → ⟨ pr a b ∈ fst (Kslot K γ) ⟩
    finSetK : (m : ℕ) (h : Fin m → V ℓ)
            → ((i : Fin m) → ⟨ h i ∈ fst (Kslot K γ) ⟩)
            → ⟨ finSet m h ∈ fst (Kslot K γ) ⟩
    carrier≡ : lookup zero γ ≡ lookup (suc (suc (suc (suc (suc (suc A)))))) γ
    envSetK : (ar : S) (m : ℕ) → fst ar ≡ # m
            → ⟨ fst ar ∈ fst (Kslot K γ) ⟩
            → ⟨ fst (Generic.envSetGen (lookup zero γ) ar) ∈ fst (Kslot K γ) ⟩

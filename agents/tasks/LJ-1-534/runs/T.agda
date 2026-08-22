{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.534] BISECTION 4.  THE SAME EIGHT HYPOTHESES, AS A PRODUCT AND
-- NOT AS A RECORD.  Runs 0, 1, 2 and 3 all walled at 8 GB and run 3 was
-- eight one-field records with nothing else.  P-x
-- (src/L/Condensation/TwelveAgree.lagda.md:126-128) says a record FIELD
-- type carrying `sucV` walls; this file removes the record and keeps
-- every token.
--
-- Baseline: runs/I.agda, the same imports and no type, 1.04 s green.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-534.runs.T {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

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

HonestFrame : {n : ℕ} (A K : Fin (5 + n)) (γ : Vec S (11 + n))
            → Type (ℓ-suc ℓ)
HonestFrame A K γ =
    isTransV (fst (Kslot K γ))
  × ⟨ fst (lookup (suc zero) γ) ∈ fst (Kslot K γ) ⟩
  × ⟨ # 0 ∈ fst (Kslot K γ) ⟩
  × ((a : V _) → ⟨ a ∈ fst (Kslot K γ) ⟩ → ⟨ sucV a ∈ fst (Kslot K γ) ⟩)
  × ((a b : V _) → ⟨ a ∈ fst (Kslot K γ) ⟩ → ⟨ b ∈ fst (Kslot K γ) ⟩
       → ⟨ pr a b ∈ fst (Kslot K γ) ⟩)
  × ((m : ℕ) (h : Fin m → V _)
       → ((i : Fin m) → ⟨ h i ∈ fst (Kslot K γ) ⟩)
       → ⟨ finSet m h ∈ fst (Kslot K γ) ⟩)
  × (lookup zero γ ≡ lookup (suc (suc (suc (suc (suc (suc A)))))) γ)
  × ((ar : S) (m : ℕ) → fst ar ≡ # m
       → ⟨ fst ar ∈ fst (Kslot K γ) ⟩
       → ⟨ fst (Generic.envSetGen (lookup zero γ) ar) ∈ fst (Kslot K γ) ⟩)

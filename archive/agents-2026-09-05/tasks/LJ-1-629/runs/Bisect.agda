{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.629] bisect file: isolate which ingredient of the c3 rows
-- leaves metas.  NOT a deliverable; the run that used it is recorded
-- and the file stays only as the record of the split.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-629.runs.Bisect {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( ω; sucV; #_ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Empty as Empty
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd )
open import L.Ordinal {ℓ} using ( ω-ord; suc-ord; mem-ord; #∈ω )
open import L.Ordinal.Linear {ℓ} lem using ( Tri; ord-tri )
open import L.Cardinal {ℓ} lem using ( IsCardinalL )
open hPropStructure 𝒮ᵥ using ( S; _∈ˢ_ )
module SL = hPropStructure 𝒮ʟ

test-∉ : (γ : S) (γ≡ω : γ ≡ ω) → (⟨ γ ∈ˢ ω ⟩ → Empty.⊥)
test-∉ _ γ≡ω = λ h → ∈-irrefl ω (subst (λ w → ⟨ w ∈ˢ ω ⟩) γ≡ω h)

test-num : (γ : S) (γ≡ω : γ ≡ ω) → ((k : ℕ) → ⟨ (# k) ∈ˢ γ ⟩)
test-num _ γ≡ω = λ k → subst (λ w → ⟨ (# k) ∈ˢ w ⟩) (sym γ≡ω) (#∈ω k)

test-mem : (κ : SL.S) (oκ : IsOrd (fst κ)) (γ : S) (γ∈κ : ⟨ γ ∈ˢ fst κ ⟩)
         → IsOrd γ
test-mem κ oκ γ γ∈κ = mem-ord {A = fst κ} oκ γ γ∈κ

test-tri : (κ : SL.S) (oκ : IsOrd (fst κ)) (γ : S) (oγ : IsOrd γ)
         → Tri (sucV γ) (fst κ)
test-tri κ oκ γ oγ = ord-tri (sucV γ) (suc-ord oγ) (fst κ) oκ

test-triω : (κ : SL.S) (oκ : IsOrd (fst κ)) (γ : S) (γ∈κ : ⟨ γ ∈ˢ fst κ ⟩)
          → Tri γ ω
test-triω κ oκ γ γ∈κ = ord-tri γ (mem-ord {A = fst κ} oκ γ γ∈κ) ω ω-ord

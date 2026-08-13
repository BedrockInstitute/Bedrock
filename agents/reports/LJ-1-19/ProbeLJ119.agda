{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.19] Cure A: restrict the limit to closure under +ω.
--
-- The existential clause's bound at arity one sits at the ω-block above
-- the carrier stage δ: the code set over the carrier has rank about δ+ω
-- (LJ-1.15's measured diagnosis).  If α is closed under +ω, then δ+ω
-- stays below α for every δ below α, and the bound lands inside Lset α.
-- The environment component at arity one sits at δ+3 (delivered EnvSet
-- stage, uniform in arity), and the finite-iterate fact lifts it too.
-- Throwaway probe; one Agda process; no git.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ119 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Model {ℓ} using ( self∈sucV )
open import L.Constructible {ℓ} using ( Lset; Lset-mono )
open import Cubical.HITs.CumulativeHierarchy.Base using ( sett )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( _∈ₛ_; ∈∈ₛ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⋃_; union-ax; module InfinitySet )
open InfinitySet using ( sucV )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- The ω-block above u: the union of the finitely iterated successors.
sucIter : ℕ → S → S
sucIter zero u = u
sucIter (suc n) u = sucV (sucIter n u)

+ω : S → S
+ω u = ⋃ (sett (Lift {ℓ-zero} {ℓ} ℕ) (λ m → sucIter (suc (lower m)) u))

-- α is closed under +ω: every member's ω-block stays inside α.
closedω : S → Type (ℓ-suc ℓ)
closedω α = (d : S) → ⟨ d ∈ˢ α ⟩ → ⟨ +ω d ∈ˢ α ⟩

-- Every finite iterate sits inside the ω-block (the δ+n < δ+ω step).
+ω-in : (u x : S) (n : ℕ) → ⟨ x ∈ˢ sucIter (suc n) u ⟩ → ⟨ x ∈ˢ +ω u ⟩
+ω-in u x n x∈ = ∈∈ₛ {a = x} {b = +ω u} .snd
  (union-ax (sett (Lift {ℓ-zero} {ℓ} ℕ) F) x .snd
    ∣ sucIter (suc n) u , (memb , x∈ₛ) ∣₁)
  where
  F : Lift {ℓ-zero} {ℓ} ℕ → S
  F m = sucIter (suc (lower m)) u
  memb : ⟨ sucIter (suc n) u ∈ₛ sett (Lift {ℓ-zero} {ℓ} ℕ) F ⟩
  memb = ∈∈ₛ {a = sucIter (suc n) u} {b = sett (Lift {ℓ-zero} {ℓ} ℕ) F} .fst
    ∣ lift n , refl ∣₁
  x∈ₛ : ⟨ x ∈ₛ sucIter (suc n) u ⟩
  x∈ₛ = ∈∈ₛ {a = x} {b = sucIter (suc n) u} .fst x∈

+ω-iter : (n : ℕ) (u : S) → ⟨ sucIter n u ∈ˢ +ω u ⟩
+ω-iter n u = +ω-in u (sucIter n u) n (self∈sucV (sucIter n u))

-- The bound at arity one: the code set over the carrier sits at δ+ω
-- (LJ-1.15's measured rank).  Under closure, δ+ω stays below α, so the
-- bound lands inside Lset α.
boundCloses : (α δ : S) (cl : closedω α) → ⟨ δ ∈ˢ α ⟩
            → (b : S) → ⟨ b ∈ˢ Lset (+ω δ) ⟩ → ⟨ b ∈ˢ Lset α ⟩
boundCloses α δ cl δ∈α b b∈ =
  Lset-mono {α = α} {β = +ω δ} (cl δ δ∈α) b∈

-- The environment component at arity one sits at δ+3 (delivered EnvSet
-- stage, uniform in arity).  The iterate fact lifts it into the ω-block,
-- and closure lands it inside Lset α.
envCloses : (α δ : S) (cl : closedω α) → ⟨ δ ∈ˢ α ⟩
          → (env : S) → ⟨ env ∈ˢ Lset (sucIter 3 δ) ⟩ → ⟨ env ∈ˢ Lset α ⟩
envCloses α δ cl δ∈α env env∈ =
  Lset-mono {α = α} {β = +ω δ} (cl δ δ∈α)
    (Lset-mono {α = +ω δ} {β = sucIter 3 δ} (+ω-iter 3 δ) env∈)

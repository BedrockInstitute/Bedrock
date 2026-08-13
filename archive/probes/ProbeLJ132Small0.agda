{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.32] Control 3: the DELIVERED count-0 reader consAtL, PLACED on its
-- own.  consAtL is a small formula (a few bounded quantifiers), count 0.
-- If this is green fast while the clause-sized count-0 matrix walls, the
-- wall is a FORMULA-SIZE wall, not a constant-count wall.
-- Untracked probe; never committed.

open import Base.Prelude
open import Base.Truth

module ProbeLJ132Small0 {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import FOL.LevyHierarchy
  using ( Δ₀; δ-∈; δ-≐; δ-∧; δ-∨; δ-⇒; δ-¬; δ-⊤; δ-⊥; δ-∀∈; δ-∃∈ )
open import FOL.Manipulation.Parameters
  using ( countFo; absFo; placeFo; padLeft )
open import FOL.Manipulation.Relabelling using ( embed; mapΔ₀ )
import Cubical.Data.Empty as Empty
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.Absoluteness {ℓ} using ( Δ₀-liftFo )
open import L.Coding.Base {ℓ} using ( Δ₀-prAt )
open import L.Coding.Environment {ℓ} using ( Δ₀-consAt )
open import L.Coding.Model {ℓ} using ( consAtL )
open import Cubical.Data.FinData using ( Fin; zero; suc )
open import Cubical.Data.Nat using ( _+_ )

open hPropStructure 𝒮ʟ

placeΔ₀ : ∀ {ℓz ℓc} {K : Type ℓc} {n k} {φ : Formula K n}
        → Δ₀ φ → (θ : Fin (countFo φ) → Fin (n + k))
        → Δ₀ (placeFo {ℓz = ℓz} φ θ)
placeΔ₀ δ-∈ θ = δ-∈
placeΔ₀ δ-≐ θ = δ-≐
placeΔ₀ (δ-∧ c d) θ = δ-∧ (placeΔ₀ c _) (placeΔ₀ d _)
placeΔ₀ (δ-∨ c d) θ = δ-∨ (placeΔ₀ c _) (placeΔ₀ d _)
placeΔ₀ (δ-⇒ c d) θ = δ-⇒ (placeΔ₀ c _) (placeΔ₀ d _)
placeΔ₀ (δ-¬ c)   θ = δ-¬ (placeΔ₀ c θ)
placeΔ₀ δ-⊤ θ = δ-⊤
placeΔ₀ δ-⊥ θ = δ-⊥
placeΔ₀ (δ-∀∈ c) θ = δ-∀∈ (placeΔ₀ c _)
placeΔ₀ (δ-∃∈ c) θ = δ-∃∈ (placeΔ₀ c _)

absΔ₀ : ∀ {ℓz ℓc} {K : Type ℓc} {n} {φ : Formula K n}
      → Δ₀ φ → Δ₀ (absFo {ℓz = ℓz} φ)
absΔ₀ {n = n} d = placeΔ₀ d (padLeft n)

Δ₀-consAtL : ∀ {n} (e' m e : Fin n) → Δ₀ (consAtL e' m e)
Δ₀-consAtL e' m e = Δ₀-liftFo _ (Δ₀-consAt e' m e)

-- The count, asserted.
_ : countFo (consAtL {1} zero zero zero) ≡ 0
_ = refl

-- The placement witness for the small count-0 reader.
σL : Formula S (1 + 0)
σL = embed (absFo {ℓz = ℓ} {ℓc = ℓ-suc ℓ} {K = S} (consAtL {1} zero zero zero))

Δ₀-σL : Δ₀ σL
Δ₀-σL = mapΔ₀ Empty.rec* (absΔ₀ {ℓz = ℓ} {ℓc = ℓ-suc ℓ} {K = S}
                          (Δ₀-consAtL {1} zero zero zero))

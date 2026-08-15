{-# OPTIONS --cubical --safe --guardedness #-}
-- [LJ-1.300] DD25 review probe for CLAIM 2, the alleged circularity.
--
-- The target says: `sq` at an ordinal comes only from `via-col-square`,
-- which consumes `Init`, whose fourth row is `noinj²`, which needs `sq`.
-- It calls that a CIRCLE.
--
-- This file measures the shape of that dependency.  It builds `sq α`
-- from the square law at the MEMBERS of alpha, strictly below alpha in
-- the membership order, plus alpha's own ambient initiality.  Nothing
-- in the term uses `sq α`.  So the dependency DESCENDS; it does not
-- return to its own ordinal.
--
-- Tracked probe.  ONE agda process under GHCRTS="-A64m -I0 -M8g".

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-300.StepProbe {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd )
open import L.Ordinal.SquareLaw {ℓ} lem using ( sq; Init; via-col-square )
open import L.BoundedSubset {ℓ} lem using ( IsCardinal )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( ω; sucV )
import Cubical.Data.Empty as Empty

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )

-- The square law at the MEMBERS of alpha only.  Every beta here is
-- strictly below alpha in the membership order.
SqBelow : V ℓ → Type (ℓ-suc ℓ)
SqBelow α = (β : V ℓ) → IsOrd β → ⟨ β ∈ˢ α ⟩ → ⟨ ω ∈ˢ β ⟩ → sq β

-- ONE STEP OF THE DESCENT.  `sq α` from `SqBelow α`.  The fourth row of
-- `Init α` is built here, and it consumes the square law at MEMBERS.
-- MEASURED: the recursion descends, so the dependency is not a cycle.
descent-step : (α : V ℓ) → IsOrd α → ⟨ ω ∈ˢ α ⟩
             → ((γ : V ℓ) → ⟨ γ ∈ˢ α ⟩ → ⟨ sucV γ ∈ˢ α ⟩)
             → IsCardinal α
             → SqBelow α
             → sq α
descent-step α oα ω∈α lim card below =
  via-col-square α (oα , ω∈α , lim , noinj)
  where
  noinj : (β : V ℓ) → IsOrd β → ⟨ β ∈ˢ α ⟩ → ⟨ ω ∈ˢ β ⟩
        → (f : ⟪ α ⟫ → ⟪ β ⟫ × ⟪ β ⟫)
        → ((m n : ⟪ α ⟫) → f m ≡ f n → m ≡ n) → Empty.⊥
  noinj β oβ β∈α ω∈β f finj = card β β∈α ((λ m → g (f m)) , hinj)
    where
    g : ⟪ β ⟫ × ⟪ β ⟫ → ⟪ β ⟫
    g = below β oβ β∈α ω∈β .fst
    gi : (p q : ⟪ β ⟫ × ⟪ β ⟫) → g p ≡ g q → p ≡ q
    gi = below β oβ β∈α ω∈β .snd
    hinj : (m n : ⟪ α ⟫) → g (f m) ≡ g (f n) → m ≡ n
    hinj m n e = finj m n (gi (f m) (f n) e)

{-# OPTIONS --cubical --safe --guardedness #-}
open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-560.runs.T1 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; con; ∃̇_; ∃̇∈ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset )
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import L.Reflect {ℓ} lem using ( Below; Wit; module Single )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )
module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- TEST 1: is the limit's ordinality reachable from outside `Single`?
t1-ord : {k : ℕ} (ψ : Formula S (suc k)) → IsOrd (Single.βω ψ)
t1-ord ψ = Single.L.top-ord ψ

-- TEST 2: is `Wit` at a stage the SAME proposition as the object-language
-- bounded existential over that stage, with NO relativization of the matrix?
t2-refl : {k : ℕ} (ψ : Formula S (suc k)) (ρ : S ^ k)
          (β : V ℓ) (oβ : IsOrd β)
        → Wit ψ ρ β ≡ (ρ ⊨ (∃̇∈ (con (LsetS β oβ)) ψ))
t2-refl ψ ρ β oβ = refl

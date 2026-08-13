{-# OPTIONS --cubical --safe --guardedness #-}

-- DD25 review probe H5: THE EXIT AT THE MATRIX AND AT THE STATEMENT.
--
-- [LJ-1.50] reports that the full `LevelHood0.matrix` variant of the
-- certificate transfer does not finish: two stop-bounded attempts, one
-- at about 570 s and one at about 520 s, both interrupted.  Its
-- verdict rests on that piece.
--
-- This probe does the SAME mathematics on the delivered `EraseTransfer`
-- route, which never calls `erase-Δ₀`:
--
--   part 1  the matrix on the EraseTransfer template
--   part 2  the Sigma-1 STATEMENT `Σ₂` moved to the parameter-free
--           axis, with the upward transfer taken on the ORIGINAL
--           certificate through `σ₁-up` and shifted by `erase-inv`
--
-- Part 2 is the adequacy connector's own obligation.  No `erase-Σ₁`
-- exists in the tree and part 2 shows none is needed.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeDD25H5 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import FOL.Syntax using ( Formula )
open import FOL.LevyHierarchy using ( Δ₀; Σ₁ )
open import FOL.Manipulation.Parameters using ( countFo )
open import FOL.Manipulation.Relabelling using ( embed )
import FOL.Count
import FOL.Absoluteness
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Condensation {ℓ} lem using ( module EraseTransfer )
open import L.BoundedSubset {ℓ} lem using ( module LevelHood0 )
open import Cubical.Data.Vec using ( map )

open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

module Cnt = FOL.Count.Count {ℓ = ℓ-suc ℓ} S

module LH0 = LevelHood0
  zero zero zero zero zero zero zero zero zero zero zero zero zero zero
  zero zero zero zero zero zero zero zero zero zero zero zero zero zero

-- =====================================================================
-- PART 1.  THE MATRIX ON THE EraseTransfer ROUTE.
-- =====================================================================

count-matrix : countFo LH0.matrix ≡ 0
count-matrix = refl

module MatrixTransfer (γ : S ^ 4) where
  module E = EraseTransfer LH0.matrix count-matrix LH0.Δ₀-matrix γ

  σL : Formula S 4
  σL = E.σL

  σL≡ : σL ≡ LH0.matrix
  σL≡ = E.σL≡

  σL-transfer : ⟨ γ ⊨ σL ⟩ ≡ ⟨ map fst γ ⊨ᵛ σL ⟩
  σL-transfer = E.σL-transfer

  σL-up : ⟨ γ ⊨ σL ⟩ → ⟨ map fst γ ⊨ᵛ σL ⟩
  σL-up = E.σL-up

-- =====================================================================
-- PART 2.  THE STATEMENT.  The Sigma-1 level-hood statement moves to
-- the parameter-free axis, and the upward transfer rides the ORIGINAL
-- certificate.  This is `EraseTransfer` one level up the hierarchy,
-- written out because the delivered template stops at Delta-0.
-- =====================================================================

count-Σ₂ : countFo LH0.Σ₂ ≡ 0
count-Σ₂ = refl

module StmtTransfer (γ : S ^ 1) where
  σL₀ : Formula (⊥* {ℓ-suc ℓ}) 1
  σL₀ = Cnt.erase LH0.Σ₂ count-Σ₂

  σL : Formula S 1
  σL = embed σL₀

  σL≡ : σL ≡ LH0.Σ₂
  σL≡ = Cnt.erase-inv LH0.Σ₂ count-Σ₂

  -- The upward transfer at the erased spelling, with `σ₁-up` taken at
  -- the ORIGINAL formula and its ORIGINAL certificate.
  σL-up : ⟨ γ ⊨ σL ⟩ → ⟨ map fst γ ⊨ᵛ σL ⟩
  σL-up h =
    subst (λ ψ → ⟨ map fst γ ⊨ᵛ ψ ⟩) (sym σL≡)
      (AbsL.σ₁-up LH0.Σ₁-Σ₂ γ (subst (λ ψ → ⟨ γ ⊨ ψ ⟩) σL≡ h))

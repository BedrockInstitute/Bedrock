{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.579] CONTROL b.  [LJ-1.560]'S REFLECTION, INSTANTIATED AT THIS
-- SITE.  The brief: "[LJ-1.560] is GO and its reflection step was an
-- instantiation of something already in the tree.  Try it here: nobody
-- has."  This file is that, and the answer is in the TYPE.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-579.runs.Control579b {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import FOL.Manipulation.Relativize using ( relativize )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset )
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import L.Reflect {ℓ} lem using ( Below )
open import L.ReflectFo {ℓ} lem using ( mkReflect )
open import LJ-1-520.Probe520 {ℓ} lem using ( levelFo-Σ₁ )

open import Cubical.Data.FinData using ( Fin )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

------------------------------------------------------------------------
-- THE INSTANTIATION.  IT TYPECHECKS, and that is the point: nothing
-- about the level formula's Σ₁ grade stops `mkReflect`.
------------------------------------------------------------------------

level-reflected :
    {n : ℕ} (w b : Fin n) (γ : V ℓ) (oγ : IsOrd γ)
  → Σ[ β ∈ V ℓ ] Σ[ oβ ∈ IsOrd β ]
      ( ⟨ γ ∈ β ⟩
      × ((ρ : S ^ n) → Below β ρ
         → (ρ ⊨ fst (levelFo-Σ₁ w b))
           ≡ (ρ ⊨ relativize (LsetS β oβ) (fst (levelFo-Σ₁ w b)))) )
level-reflected w b γ oγ = mkReflect (fst (levelFo-Σ₁ w b)) γ oγ

------------------------------------------------------------------------
-- AND WHAT THE OBLIGATION NEEDS IS THE SAME SENTENCE AT `γ` ITSELF,
-- WITH NO NEW ORDINAL AT ALL.  Stated, NOT inhabited, and it is not a
-- weakening of the row above: it is a different statement.
------------------------------------------------------------------------

LevelAtGamma : Type (ℓ-suc (ℓ-suc ℓ))
LevelAtGamma = {n : ℕ} (w b : Fin n) (γ : V ℓ) (oγ : IsOrd γ)
             → (ρ : S ^ n) → Below γ ρ
             → (ρ ⊨ fst (levelFo-Σ₁ w b))
               ≡ (ρ ⊨ relativize (LsetS γ oγ) (fst (levelFo-Σ₁ w b)))

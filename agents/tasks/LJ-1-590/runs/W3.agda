{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.590] W3, ALONE, TYPECHECKED BEFORE ANY OTHER AGDA OF THIS TASK.
--
-- The brief's W3 is "[LJ-1.560]'s obligation, at StageOfCode's frame,
-- TYPE ONLY".  Three types and no new term.
--
--   1a  [LJ-1.560]'s `search-bounds` re-ascribed here
--       (agents/tasks/LJ-1-560/Probe560.agda:165-176).
--   1b  the ONE shape StageOfCode asks for, written as a type family:
--       an ordinal AS DATA out of a TRUNCATED existence of one.
--   1c  the tree's device that HAS shape 1b: `L.Stage.leastOrd`
--       (src/L/Stage.lagda.md:149-153), re-ascribed, by name.
--
-- READ 1a AGAINST 1b: `search-bounds` hands back its beta from PSI
-- ALONE, and then charges `Below beta rho` for every environment.
-- StageOfCode's beta must be a function of `a` and `b`, and StageOfCode
-- offers no `Below` hypothesis at all.  That is the difference, and 1c
-- is where the shape actually lives.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-590.runs.W3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; ∃̇_ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; IsOrd )
open import L.Reflect {ℓ} lem using ( Below; Wit; SatEx; module Single )
open import L.Stage {ℓ} lem using ( isLeastOrd; leastOrd )

open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- 1a.  [LJ-1.560]'s OBLIGATION, RE-ASCRIBED, TYPE ONLY.  The term is
--      `Single.reflect`'s bundle and is not rebuilt here.
SearchBoundsHere : Type (ℓ-suc ℓ)
SearchBoundsHere =
  {k : ℕ} (ψ : Formula S (suc k))
  → Σ[ β ∈ V ℓ ] Σ[ oβ ∈ IsOrd β ]
      ((ρ : S ^ k) → Below β ρ → ⟨ ρ ⊨ (∃̇ ψ) ⟩ → ⟨ Wit ψ ρ β ⟩)

search-bounds-here : SearchBoundsHere
search-bounds-here ψ = Single.βω ψ , Single.L.top-ord ψ , Single.closed ψ

-- 1b.  THE SHAPE StageOfCode ASKS FOR, with its predicate abstract.
--      Compare it with 1a: no formula, no environment, no `Below`.
StageShape : Type (ℓ-suc (ℓ-suc ℓ))
StageShape = (P : V ℓ → Ω)
           → ∥ (Σ[ α ∈ V ℓ ] (IsOrd α × ⟨ P α ⟩)) ∥₁
           → Σ[ α ∈ V ℓ ] Σ[ _ ∈ IsOrd α ] ⟨ P α ⟩

-- 1c.  AND THE TREE HAS IT.  src/L/Stage.lagda.md:149-153, by name.
stage-shape : StageShape
stage-shape P h = α , oα , pα
  where
  ℓo : Σ[ α ∈ V ℓ ] (IsOrd α × ⟨ P α ⟩ × isLeastOrd P α)
  ℓo = leastOrd P h
  α = ℓo .fst
  oα = ℓo .snd .fst
  pα = ℓo .snd .snd .fst

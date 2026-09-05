{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.560] W3.  THE WIDEST UNMEASURED TERM, TYPE ONLY.
--
-- WRITTEN FIRST AND TYPECHECKED ALONE, before any other Agda of this
-- task, exactly as the brief orders.  No hole, no postulate.
--
-- The brief names the widest unmeasured term:
--
--     -- the chapter's strongest statement about a formula holding at a
--     -- stage, re-ascribed, TYPE ONLY
--
-- ANSWER: the tree carries TWO such statements, not one, and the second
-- is strictly stronger than anything this task's obligation asks for.
--
--   w3-single  re-ascribes  L.Reflect.Single.reflect
--              (src/L/Reflect.lagda.md:520).  One matrix, one
--              existential, a limit built for that matrix alone.
--              Its right-hand side `Wit` is META-level.
--
--   w3-full    re-ascribes  L.ReflectFo.mkReflect
--              (src/L/ReflectFo.lagda.md:525).  ANY formula, ANY
--              complexity, plus an ordinal the caller needs inside the
--              stage.  Its right-hand side is a FORMULA, and
--              `Δ₀-relativize` (src/FOL/Manipulation/Relativize.lagda.md:72)
--              grades that formula Δ₀ with no side condition at all.
--
-- Neither term is written here.  Both are the library's own, re-ascribed
-- at the type the obligation would have to inhabit, so the D-10 is read
-- off a typecheck and not off the chapter's prose.
--
-- CALIBER.  The program set GHCRTS="-A64m -I0 -M8g" on this pane.  I
-- did not set it.  One Agda process at a time.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-560.runs.W3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; ∃̇_ )
open import FOL.LevyHierarchy using ( Δ₀ )
open import FOL.Manipulation.Relativize using ( relativize; Δ₀-relativize )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; IsOrd )
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import L.Reflect {ℓ} lem using ( Below; Wit; module Single )
open import L.ReflectFo {ℓ} lem using ( mkReflect )

open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- 1.  ONE MATRIX.  The limit of the single-matrix ladder answers the
--     existential for every environment drawn from it.  META-level
--     conclusion: `Wit` is a truncated sum over the L-carrier, cut down
--     by an Agda-level membership in `Lset`.
w3-single : {k : ℕ} (ψ : Formula S (suc k)) (ρ : S ^ k)
          → Below (Single.βω ψ) ρ
          → (ρ ⊨ (∃̇ ψ)) ≡ Wit ψ ρ (Single.βω ψ)
w3-single ψ = Single.reflect ψ

-- 2.  ANY FORMULA.  OBJECT-level conclusion: the right-hand side is a
--     `Formula S n`, and the stage enters it as a CONSTANT.
w3-full : {n : ℕ} (φ : Formula S n) (δ : V ℓ) → IsOrd δ
        → Σ[ β ∈ V ℓ ] Σ[ oβ ∈ IsOrd β ]
            ( ⟨ δ ∈ β ⟩
            × ((γ : S ^ n) → Below β γ
               → (γ ⊨ φ) ≡ (γ ⊨ relativize (LsetS β oβ) φ)) )
w3-full = mkReflect

-- 3.  AND THE GRADE IS FREE.  No hypothesis on φ, none on the stage.
w3-grade : {n : ℕ} (β : V ℓ) (oβ : IsOrd β) (φ : Formula S n)
         → Δ₀ (relativize (LsetS β oβ) φ)
w3-grade β oβ φ = Δ₀-relativize (LsetS β oβ) φ

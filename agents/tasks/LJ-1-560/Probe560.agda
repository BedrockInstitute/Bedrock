{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.560]  Bound one unbounded search to a stage.
--
-- W3 IS SECTION 1, AND IT WAS WRITTEN FIRST AND TYPECHECKED ALONE.
-- The slice is agents/tasks/LJ-1-560/runs/W3.agda, run w3-1.out to
-- w3-3.out, exit 0.
--
-- THE OBLIGATION IS INHABITED.  `search-bounds` is section 3.  This
-- file carries NO hole and NO postulate, so every reduction in it is a
-- measurement and not a claim ([LJ-1.533]'s discipline, kept by
-- [LJ-1.549], [LJ-1.552] and [LJ-1.557]).  Nothing lands in src/.
--
-- THE HEADLINE, AND IT IS A D-10.  The brief asked whether
-- src/L/Reflect.lagda.md already proves a reflection principle.  IT
-- DOES, AND SO DOES ITS SUCCESSOR, AND THE SUCCESSOR IS ALREADY SPENT
-- IN src/.  This task is an INSTANTIATION and not a construction.  The
-- obligation below is `Single.reflect` re-ascribed at the type the
-- brief names, plus one `refl`.
--
-- WHAT THIS FILE MEASURES, IN ONE LINE EACH.
--
--   Section 1.  W3.  The two reflection principles the tree already
--               carries, re-ascribed, TYPE ONLY.  `Single.reflect`
--               (one matrix, matrix untouched) and `mkReflect` (any
--               formula, any complexity, plus a caller-chosen ordinal
--               inside the stage, matrix relativized).
--   Section 2.  THE BOUNDARY IS NOT THERE.  `Wit ψ ρ β`, the meta-level
--               search cut down to `Lset β`, IS the object-language
--               bounded existential `∃̇∈ (con (LsetS β oβ)) ψ` read at
--               that stage.  BY `refl`.  Nothing is paid to cross.
--   Section 3.  THE OBLIGATION.  `search-bounds`: for any formula with
--               one witness variable and k parameters, a stage whose
--               `Lset` answers the unbounded existential, stated three
--               ways at one stage.
--   Section 4.  THE TRADE.  Σ₁ in, Δ₀ out: the bounded form is Δ₀ as
--               soon as the matrix is, by `δ-∃∈` and nothing else.
--   Section 5.  THE DOOR IS ALREADY WRAPPED, TWICE.  `AtStage` wants
--               Δ₀ AND `BoundedFo`; `separateΔ₀` discharges the second
--               for every formula, and `hasSeparationL` discharges the
--               first as well.  Neither is this task's obligation and
--               both are re-ascribed here, TYPE ONLY, because they are
--               what [LJ-1.536]'s NO-GO was measured against.
--
-- CALIBER.  The program set GHCRTS="-A64m -I0 -M8g" on this pane.  I
-- did not set it.  One Agda process at a time.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-560.Probe560 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; con; ∃̇_; ∃̇∈ )
open import FOL.LevyHierarchy using ( Δ₀; δ-∃∈; Σ₁; σ-Δ₀; σ-∃ )
open import FOL.Manipulation.Bounding using ( BoundedFo )
open import FOL.Manipulation.Relativize using ( relativize; Δ₀-relativize )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset )
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import L.Axioms.Separation {ℓ} lem using ( Below′; mkBoundedFo; separateΔ₀ )
open import L.Axioms.Full {ℓ} lem using ( hasSeparationL )
import FOL.ZFModel
open import L.Reflect {ℓ} lem using ( Below; Wit; SatEx; module Single )
open import L.ReflectFo {ℓ} lem using ( mkReflect )

open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )
module ModelL = FOL.ZFModel 𝒮ʟ
open ModelL using ( SetOf )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

------------------------------------------------------------------------
-- SECTION 1.  W3.  WHAT `L.Reflect` ALREADY HAS.
--
-- Written first, in agents/tasks/LJ-1-560/runs/W3.agda, and typechecked
-- alone before any other Agda of this task.  Restated here so the file
-- stands on its own.
------------------------------------------------------------------------

-- 1a.  ONE MATRIX.  src/L/Reflect.lagda.md:520.  The limit of the
--      single-matrix ladder answers the existential for every
--      environment drawn from it.  THE MATRIX IS NOT TOUCHED.
w3-single : {k : ℕ} (ψ : Formula S (suc k)) (ρ : S ^ k)
          → Below (Single.βω ψ) ρ
          → (ρ ⊨ (∃̇ ψ)) ≡ Wit ψ ρ (Single.βω ψ)
w3-single ψ = Single.reflect ψ

-- 1b.  ANY FORMULA, AND AN ORDINAL THE CALLER NEEDS INSIDE THE STAGE.
--      src/L/ReflectFo.lagda.md:525.  THE MATRIX IS RELATIVIZED, and
--      the price of that is section 3's `keeps-matrix` column.
w3-full : {n : ℕ} (φ : Formula S n) (δ : V ℓ) → IsOrd δ
        → Σ[ β ∈ V ℓ ] Σ[ oβ ∈ IsOrd β ]
            ( ⟨ δ ∈ β ⟩
            × ((γ : S ^ n) → Below β γ
               → (γ ⊨ φ) ≡ (γ ⊨ relativize (LsetS β oβ) φ)) )
w3-full = mkReflect

-- 1c.  AND THE GRADE IS FREE.  No hypothesis on φ, none on the stage.
--      src/FOL/Manipulation/Relativize.lagda.md:72.
w3-grade : {n : ℕ} (β : V ℓ) (oβ : IsOrd β) (φ : Formula S n)
         → Δ₀ (relativize (LsetS β oβ) φ)
w3-grade β oβ φ = Δ₀-relativize (LsetS β oβ) φ

------------------------------------------------------------------------
-- SECTION 2.  THE BOUNDARY IS NOT THERE.
--
-- The brief warns that a term bounding a META-level search proves
-- nothing about `defSet`, and that four earlier tasks stopped at that
-- boundary.  At a STAGE the boundary is not a boundary: the chapter's
-- `Wit` and the object language's bounded existential are the same
-- proposition, definitionally, because `LsetS β oβ` keeps its first
-- component reducing (src/L/ReflectFo.lagda.md:88-96 says why that is
-- deliberate) and the model's membership is the ambient one on the
-- first components.
------------------------------------------------------------------------

-- The object-language bounding operator: one constant, one bounded ∃.
boundAt : {k : ℕ} (φ : Formula S (suc k)) (β : V ℓ) → IsOrd β → Formula S k
boundAt φ β oβ = ∃̇∈ (con (LsetS β oβ)) φ

-- AND THE IDENTIFICATION IS `refl`, AT EVERY STAGE AND EVERY FORMULA.
wit-is-object : {k : ℕ} (ψ : Formula S (suc k)) (ρ : S ^ k)
                (β : V ℓ) (oβ : IsOrd β)
              → Wit ψ ρ β ≡ (ρ ⊨ boundAt ψ β oβ)
wit-is-object ψ ρ β oβ = refl

-- The same for the unbounded side, so both halves of section 3 are
-- read in the object language and neither is an Agda paraphrase.
satex-is-object : {k : ℕ} (ψ : Formula S (suc k)) (ρ : S ^ k)
                → SatEx ψ ρ ≡ (ρ ⊨ (∃̇ ψ))
satex-is-object ψ ρ = refl

------------------------------------------------------------------------
-- SECTION 3.  THE OBLIGATION.
--
--     search-bounds :
--       <given a predicate on L-sets that is satisfied somewhere in L,
--        a stage β whose Lset already holds a witness>
--
-- THE PREDICATE'S FORM, STATED AS GENERALLY AS IT IS TRUE: an arbitrary
-- `Formula S (suc k)`.  One witness variable, `k` parameters, NO Levy
-- grade, NO bound on the quantifiers already inside it, NO hypothesis
-- that the parameters are anything but members of the stage.  "Satisfied
-- somewhere in L" is `ρ ⊨ ∃̇ ψ`: the object language's own unbounded
-- existential, read by the world's INNER satisfaction, which is the
-- same `_⊨ᵐ_` that `defSet` reads (src/L/Definability.lagda.md:111).
--
-- THE CONCLUSION IS STATED THREE WAYS AT ONE STAGE, because the three
-- are what three different consumers need:
--   `holds`  the witness lies in `Lset β`.  Truncated, as the brief
--            allows; this is the obligation's own sentence.
--   `objec`  the unbounded existential EQUALS a bounded one, as
--            formulas, at every environment drawn from the stage.
--   `grade`  and that bounded one is Δ₀ as soon as the matrix is.
------------------------------------------------------------------------

search-bounds :
  {k : ℕ} (ψ : Formula S (suc k))
  → Σ[ β ∈ V ℓ ] Σ[ oβ ∈ IsOrd β ]
      ( ((ρ : S ^ k) → Below β ρ → ⟨ ρ ⊨ (∃̇ ψ) ⟩ → ⟨ Wit ψ ρ β ⟩)
      × ((ρ : S ^ k) → Below β ρ → (ρ ⊨ (∃̇ ψ)) ≡ (ρ ⊨ boundAt ψ β oβ))
      × (Δ₀ ψ → Δ₀ (boundAt ψ β oβ)) )
search-bounds ψ =
    Single.βω ψ
  , Single.L.top-ord ψ
  , ( Single.closed ψ
    , Single.reflect ψ
    , δ-∃∈ )

------------------------------------------------------------------------
-- SECTION 4.  THE TRADE, NAMED.
--
-- Premise 7 of the brief: Σ₁ has an unbounded-quantifier constructor
-- (src/FOL/LevyHierarchy.lagda.md:75).  That constructor is the ONE
-- thing section 3 removes.  A Σ₁ formula built as one `σ-∃` over a Δ₀
-- matrix is traded for a Δ₀ formula and a named stage, and the trade is
-- an EQUALITY of truth values, not an implication.
------------------------------------------------------------------------

sigma-one : {k : ℕ} (ψ : Formula S (suc k)) → Δ₀ ψ → Σ₁ (∃̇ ψ)
sigma-one ψ dψ = σ-∃ (σ-Δ₀ dψ)

trade : {k : ℕ} (ψ : Formula S (suc k)) → Δ₀ ψ
      → Σ[ β ∈ V ℓ ] Σ[ oβ ∈ IsOrd β ]
          ( Δ₀ (boundAt ψ β oβ)
          × ((ρ : S ^ k) → Below β ρ → (ρ ⊨ (∃̇ ψ)) ≡ (ρ ⊨ boundAt ψ β oβ)) )
trade ψ dψ = Single.βω ψ , Single.L.top-ord ψ , (δ-∃∈ dψ , Single.reflect ψ)

------------------------------------------------------------------------
-- SECTION 5.  THE DOOR, RE-ASCRIBED.  TYPE ONLY, NOT THE OBLIGATION.
--
-- [LJ-1.536] is a NO-GO because `AtStage`'s first hypothesis is Δ₀
-- (src/L/Axioms/Separation.lagda.md:199-206).  That is true OF
-- `AtStage`, and `AtStage` is not the only door.  Two wrappers stand in
-- front of it in src/ today and each one drops a hypothesis.
------------------------------------------------------------------------

-- 5a.  `BoundedFo` is free for every formula: the recursion produces the
--      stage that bounds the constants.  src/L/Axioms/Separation.lagda.md:449.
door-bounded : {n : ℕ} (φ : Formula S n)
             → Σ[ σ ∈ V ℓ ] (IsOrd σ × BoundedFo (Below′ σ) φ)
door-bounded = mkBoundedFo

-- 5b.  So separation at a Δ₀ formula needs the Δ₀ WITNESS AND NOTHING
--      ELSE: no stage, no `BoundedFo`, no `𝒟ₒ-intro` by hand.
--      src/L/Axioms/Separation.lagda.md:481.
door-delta0 : (a : S) (φ : Formula S 1) → Δ₀ φ
            → isContr (SetOf (λ x → (x ∈ˢ a) ⊓ ((x ∷ []) ⊨ φ)))
door-delta0 = separateΔ₀

-- 5c.  AND THE Δ₀ HYPOTHESIS IS GONE TOO.  Separation in L holds at an
--      ARBITRARY formula, by reflecting it and separating with the
--      relativization.  src/L/Axioms/Full.lagda.md:144.  This is
--      section 1b spent once, in src/, already.
door-any : (a : S) (φ : Formula S 1)
         → isContr (SetOf (λ x → (x ∈ˢ a) ⊓ ((x ∷ []) ⊨ φ)))
door-any = hasSeparationL

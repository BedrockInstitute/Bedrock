{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.232] probe A3.  Does `stageBound` supply β for free?
--
-- [LJ-1.134] Part B fixed β as a PARAMETER
-- (agents/tasks/LJ-1-134/lj-1.134-report.md:238):
--
--     module Least (β : V ℓ) (oβ : IsOrd β) (D : S) where
--
-- A master must produce β from `stageBound`
-- (src/L/Choice/Stage.lagda.md:328), which is delivered.  This probe
-- replaces the parameter by the value `stageBound` returns, and checks
-- the canonical selection `leastOf (orderAt β) Good h` elaborates with
-- NO β hypothesis.
--
--   S1  `injAt` with `injAt-out` and `injAt-in`, copied from
--       [LJ-1.229]'s `ProbeLJ1229A.agda` (A2's S1).  NOT rewritten.
--   A3  `Canonical`: β from `stageBound (fst a) (snd a)`, the crossing
--       `up`, the `Good` predicate over A2's `svAt`, `domAt`, `injAt`,
--       and the selection `leastOf (orderAt β oβ) lem Good h`.
--   G   the C-38 guard: `stageBound` at a REAL ordinal (ω), showing β
--       is produced, not assumed.
--
-- Probe only.  Nothing lands in src/.  ONE agda process under
-- GHCRTS="-A64m -I0 -M8g"; never committed.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-232.ProbeLJ1232A3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; var; con; _∈̇_; _≐_; _∧̇_; _⇒̇_; ∀̇_ )
import FOL.Absoluteness
import FOL.ZFModel
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; Lset→isL )
open import L.Ordinal {ℓ} using ( ω-ord; suc-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.Choice.Stage {ℓ} lem using ( stageBound )
open import L.Choice.Step {ℓ} lem using ( Mem; orderAt )
open import L.WellOrder.Base {ℓ-suc ℓ}
  using ( SWO; IsLeast; leastOf )
open import L.Coding.Model {ℓ}
  using ( appAt; appAt-adequate; svAt; svAt-out; svAt-in
        ; domAt; domAt-in; domAt-out )
open import V.Presentation {ℓ} using ( member )

open import Cubical.Data.Sigma using ( Σ≡Prop )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( ω; sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )
open hPropStructure 𝒮ʟ using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

-- ---------------------------------------------------------------------
-- S1.  Injectivity of a graph, in the object language.  Copied from
-- [LJ-1.229] ProbeLJ1229A.agda, unchanged.
-- ---------------------------------------------------------------------

injAt : ∀ {n} → Fin n → Formula S n
injAt f = ∀̇ (∀̇ (∀̇ (
      appAt (suc (suc (suc f))) (suc zero) (suc (suc zero))
  ⇒̇ (appAt (suc (suc (suc f))) zero (suc (suc zero))
  ⇒̇ (var (suc zero) ≐ var zero)))))

module _ {n : ℕ} (f : Fin n) (γ : S ^ n) where
  private
    Holds₀ : S → S → Type (ℓ-suc ℓ)
    Holds₀ x y = ⟨ pr (fst x) (fst y) ∈ fst (lookup f γ) ⟩

    at₁ : (y x x' : S)
        → ((x' ∷ x ∷ y ∷ γ) ⊨ appAt (suc (suc (suc f))) (suc zero) (suc (suc zero)))
        ≡ (pr (fst x) (fst y) ∈ fst (lookup f γ))
    at₁ y x x' = appAt-adequate (suc (suc (suc f))) (suc zero) (suc (suc zero))
                   (x' ∷ x ∷ y ∷ γ)

    at₂ : (y x x' : S)
        → ((x' ∷ x ∷ y ∷ γ) ⊨ appAt (suc (suc (suc f))) zero (suc (suc zero)))
        ≡ (pr (fst x') (fst y) ∈ fst (lookup f γ))
    at₂ y x x' = appAt-adequate (suc (suc (suc f))) zero (suc (suc zero))
                   (x' ∷ x ∷ y ∷ γ)

  injAt-out : ⟨ γ ⊨ injAt f ⟩
            → (y x x' : S) → Holds₀ x y → Holds₀ x' y → fst x ≡ fst x'
  injAt-out h y x x' p q = h y x x'
    (subst ⟨_⟩ (sym (at₁ y x x')) p) (subst ⟨_⟩ (sym (at₂ y x x')) q)

  injAt-in : ((y x x' : S) → Holds₀ x y → Holds₀ x' y → fst x ≡ fst x')
           → ⟨ γ ⊨ injAt f ⟩
  injAt-in h y x x' p q = h y x x'
    (subst ⟨_⟩ (at₁ y x x') p) (subst ⟨_⟩ (at₂ y x x') q)

-- ---------------------------------------------------------------------
-- A3.  The canonical selection, β supplied by stageBound.
--   Compare [LJ-1.134] ProbeLJ1134A `Least`, which took β and oβ as
--   parameters.  Here they are PRODUCED from stageBound, so the module
--   has NO β hypothesis.
-- ---------------------------------------------------------------------

module Canonical (a : S) (D : S) where

  β : V ℓ
  β = stageBound (fst a) (snd a) .fst

  oβ : IsOrd β
  oβ = stageBound (fst a) (snd a) .snd .fst

  ω∈β : ⟨ ω ∈ˢ β ⟩
  ω∈β = stageBound (fst a) (snd a) .snd .snd .fst

  -- The crossing: a member of the tower at β is an L-element.
  up : Mem (Lset β) → S
  up (x , m) = x , Lset→isL β oβ x m

  -- A2's predicate, over the graph carried by a member of the tower.
  Good : Mem (Lset β) → Ω
  Good A = ((up A ∷ D ∷ []) ⊨ svAt zero)
         ⊓ (((up A ∷ D ∷ []) ⊨ domAt zero (suc zero))
         ⊓  ((up A ∷ D ∷ []) ⊨ injAt zero))

  -- The canonical selection.  NO β hypothesis: β came from stageBound.
  module _ (h : ∥ Σ[ A ∈ Mem (Lset β) ] ⟨ Good A ⟩ ∥₁) where

    chosen : Σ[ A ∈ Mem (Lset β) ] IsLeast (orderAt β oβ) Good A
    chosen = leastOf (orderAt β oβ) lem Good h

    F₀ : S
    F₀ = up (fst chosen)

    good : ⟨ Good (fst chosen) ⟩
    good = fst (snd chosen)

    sv : ⟨ (F₀ ∷ D ∷ []) ⊨ svAt zero ⟩
    sv = fst good

    dm : ⟨ (F₀ ∷ D ∷ []) ⊨ domAt zero (suc zero) ⟩
    dm = fst (snd good)

    ij : ⟨ (F₀ ∷ D ∷ []) ⊨ injAt zero ⟩
    ij = snd (snd good)

-- ---------------------------------------------------------------------
-- G.  The C-38 guard: stageBound at a REAL ordinal.  ω is an L-ordinal,
-- and stageBound ω hω PRODUCES β with IsOrd β and ω ∈ β, no hypothesis.
-- ---------------------------------------------------------------------

module Atω where

  hω : ⟨ isL ω ⟩
  hω = Lset→isL (sucV ω) (suc-ord ω-ord) ω (ord∈Lset-suc ω ω-ord)

  aω : S
  aω = ω , hω

  β : V ℓ
  β = stageBound (fst aω) (snd aω) .fst

  oβ : IsOrd β
  oβ = stageBound (fst aω) (snd aω) .snd .fst

  ω∈β : ⟨ ω ∈ˢ β ⟩
  ω∈β = stageBound (fst aω) (snd aω) .snd .snd .fst

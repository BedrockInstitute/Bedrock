{-# OPTIONS --cubical --safe --guardedness #-}

-- [DD25 review of LJ-1.34] Two isolations.
--
-- EXPERIMENT A.  `src/ProbeDD25D1.agda` moved every second of the leg-D
-- agreement into two endpoint conversion checks, 14.9 s and 14.5 s.
-- This probe splits that conversion into its pieces, so the orchestrator
-- knows what the irreducible endpoint costs and what it does not.
--   A1: the FORMULA-level identity, by refl.  No satisfaction anywhere.
--   A2: the SATISFACTION-level identity on the delivered clause.
--   A3: the SATISFACTION-level identity on the bound hypotheses.
--
-- EXPERIMENT B.  The return's obstruction 2 says the story's own `extAt`
-- wrappers are two unbounded universals each, so the story cannot be
-- Delta-0 (`_build/lj-1.34-report.md:53-56`).  This probe writes the
-- BOUNDED ext and closes its Delta-0 certificate, the way the delivered
-- `src/L/Condensation.lagda.md:132-194` writes its own bounded clause.
-- It then closes the WHOLE bounded story clause's certificate from ONE
-- premise: a Delta-0 witness for the leaf content.
--
-- Untracked probe; one Agda process under GHCRTS="-A64m -I0 -M8g";
-- never committed; thrown away per D-1.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeDD25D2 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; var; _∈̇_; _∧̇_; _⇒̇_; ∃̇_; ∀̇_; ∃̇∈; ∀̇∈ )
open import FOL.LevyHierarchy
  using ( Δ₀; δ-∈; δ-∧; δ-⇒; δ-∀∈; δ-∃∈ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans )
open import L.Absoluteness {ℓ} using ( Δ₀-liftFo )
open import L.Coding.Base {ℓ} using ( Δ₀-prAt )
open import L.Coding.Model {ℓ}
  using ( prAtL; appAt; extAt )
open import L.Coding.Powerset {ℓ} lem
  using ( DefAt; DefBody )
open import L.Coding.Sequence {ℓ} lem
  using ( StepAt; StepBody )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

-- =====================================================================
-- EXPERIMENT A: WHAT THE ENDPOINT CONVERSION COSTS.
-- =====================================================================

-- The generic clause shape, ψ a variable.  Same as ProbeDD25D1.G.
module GC {n : ℕ} (ψ : Formula S (suc (suc (suc (5 + n))))) (v b f : Fin n)
  where
  private
    V₁ B₁ F₁ : Fin (suc n)
    V₁ = suc v
    B₁ = suc b
    F₁ = suc f

  LeafD : Formula S (5 + n)
  LeafD = extAt zero (∃̇ (∃̇ ψ))

  BodyD : Formula S (5 + n)
  BodyD =
    (var (suc (suc zero)) ∈̇ var (suc (suc (suc (suc B₁)))))
    ∧̇ ( appAt (suc (suc (suc (suc F₁)))) (suc (suc zero)) (suc zero)
      ∧̇ ( LeafD ∧̇ (var (suc (suc (suc zero))) ∈̇ var zero) ) )

  ClauseD : Formula S (suc n)
  ClauseD = extAt V₁ (∃̇ (∃̇ (∃̇ BodyD)))

module ConvCost {n : ℕ} (v b f : Fin n) (γ : S ^ suc n) where
  private
    V₁ B₁ F₁ : Fin (suc n)
    V₁ = suc v
    B₁ = suc b
    F₁ = suc f

    module GG = GC {n} (DefBody (suc zero)) v b f

  -- A1.  FORMULA level only.  No satisfaction.
  a1-formula : StepAt V₁ B₁ F₁ ≡ GG.ClauseD
  a1-formula = refl

  -- A2.  SATISFACTION level, the delivered clause, one direction.
  a2-sat-out : ⟨ γ ⊨ GG.ClauseD ⟩ → ⟨ γ ⊨ StepAt V₁ B₁ F₁ ⟩
  a2-sat-out h = h

  a2-sat-in : ⟨ γ ⊨ StepAt V₁ B₁ F₁ ⟩ → ⟨ γ ⊨ GG.ClauseD ⟩
  a2-sat-in h = h

  -- A3.  SATISFACTION level, the bound hypothesis on the delivered body.
  a3-bnd : (z c w d : S)
         → ⟨ (d ∷ w ∷ c ∷ z ∷ γ) ⊨ GG.BodyD ⟩
         → ⟨ (d ∷ w ∷ c ∷ z ∷ γ) ⊨ StepBody B₁ F₁ ⟩
  a3-bnd z c w d h = h

  -- A4.  SATISFACTION level, the leaf alone.
  a4-leaf : (δ : S ^ (5 + n))
          → ⟨ δ ⊨ GG.LeafD ⟩ → ⟨ δ ⊨ DefAt zero (suc zero) ⟩
  a4-leaf δ h = h

-- =====================================================================
-- EXPERIMENT B: THE BOUNDED EXT, AND OBSTRUCTION 2.
-- =====================================================================

-- `extAt y φ = ∀̇ (z ∈ y ⇒̇ φ) ∧̇ ∀̇ (φ ⇒̇ z ∈ y)`
--   (src/L/Coding/Model.lagda.md:662-664).  Two unbounded universals.
-- The FIRST is a bounded universal written unbounded: its hypothesis IS
-- the bound.  The SECOND needs a set that holds every satisfier, and the
-- story already carries one, the bound slot K.
extAtB : ∀ {n} → Fin n → Fin n → Formula S (suc n) → Formula S n
extAtB y K φ = ∀̇∈ (var y) φ
             ∧̇ ∀̇∈ (var K) (φ ⇒̇ (var zero ∈̇ var (suc y)))

Δ₀-extAtB : ∀ {n} (y K : Fin n) (φ : Formula S (suc n))
          → Δ₀ φ → Δ₀ (extAtB y K φ)
Δ₀-extAtB y K φ d = δ-∧ (δ-∀∈ d) (δ-∀∈ (δ-⇒ d δ-∈))

-- The delivered atom witnesses, as `src/L/Condensation.lagda.md:151-156`
-- builds them.
Δ₀-prAtL : ∀ {m} (q u v : Fin m) → Δ₀ (prAtL q u v)
Δ₀-prAtL q u v = Δ₀-liftFo _ (Δ₀-prAt q u v)

Δ₀-appAt : ∀ {m} (f x y : Fin m) → Δ₀ (appAt f x y)
Δ₀-appAt f x y = δ-∃∈ (Δ₀-prAtL zero (suc x) (suc y))

-- The FULLY bounded story clause: every ext is `extAtB`, every
-- existential is `∃̇∈`.  The leaf CONTENT is still the delivered
-- `DefBody`, so its certificate stays a premise.
module StoryBB {n : ℕ} (v b f : Fin n) where
  private
    K V₁ B₁ F₁ : Fin (suc n)
    K  = zero
    V₁ = suc v
    B₁ = suc b
    F₁ = suc f

    KB : Fin (5 + n)
    KB = suc (suc (suc (suc zero)))

  LeafBB : Formula S (5 + n)
  LeafBB = extAtB zero KB
    (∃̇∈ (var (suc KB)) (∃̇∈ (var (suc (suc KB))) (DefBody (suc zero))))

  BodyBB : Formula S (5 + n)
  BodyBB =
    (var (suc (suc zero)) ∈̇ var (suc (suc (suc (suc B₁)))))
    ∧̇ ( appAt (suc (suc (suc (suc F₁)))) (suc (suc zero)) (suc zero)
      ∧̇ ( LeafBB ∧̇ (var (suc (suc (suc zero))) ∈̇ var zero) ) )

  WitBB : Formula S (suc (suc n))
  WitBB =
    ∃̇∈ (var (suc (suc b)))
      (∃̇∈ (var (suc (suc K)))
        (∃̇∈ (var (suc (suc (suc K))))
          BodyBB))

  ClauseBB : Formula S (suc n)
  ClauseBB = extAtB V₁ K WitBB

  -- THE POINT.  ONE premise, and it is the leaf content.  Every
  -- quantifier of the story's own shape is bounded and certified.
  Δ₀-clause : Δ₀ (DefBody {5 + n} (suc zero)) → Δ₀ ClauseBB
  Δ₀-clause dleaf =
    Δ₀-extAtB V₁ K WitBB
      (δ-∃∈ (δ-∃∈ (δ-∃∈
        (δ-∧ δ-∈
          (δ-∧ (Δ₀-appAt (suc (suc (suc (suc F₁)))) (suc (suc zero)) (suc zero))
            (δ-∧ (Δ₀-extAtB zero KB _ (δ-∃∈ (δ-∃∈ dleaf)))
                 δ-∈))))))

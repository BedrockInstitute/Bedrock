{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.731] PROBE.  Sat-in-carrier-stage, the value bound DefAt's second
--                     existential consumes.  Lands nothing in src/.
--
--   OBLIGATION  Sat-in-carrier-stage, stated verbatim at the file's top
--               level as a TYPE.  NOT INHABITED.  The D-10 check against
--               this target found it FALSE at the intended generality:
--               the type quantifies over ALL Formula S n, and a formula
--               may carry a constant c that no hypothesis places in
--               Lset gamma.  At gamma = sucV omega and A = LsetS omega,
--               phi = (var zero IN con c), the recursion's value is the
--               c-trace of the carrier's values, and for c whose part
--               over the carrier is new above gamma that trace does not
--               sit in Lset gamma.  Section 2 is the machine-checked
--               core of the refutation: membership in
--               Sat B (var zero IN con c) at an environment IS the
--               c-trace fact, one PT.rec each way, from the landed
--               readers alone.  review-of-Sat-in-carrier-stage.md
--               carries the full argument and the corrected target.
--
--   DELIVERED   cond-trace-equiv: the c-trace reduction, generic in the
--                 carrier B and the unplaced constant c, both directions.
--   ABSENT      the INHABITANT of Sat-in-carrier-stage.  No postulate
--               stands in for it and no weaker form is inhabited under
--               its name.  The file carries --safe.
--
-- ONE Agda process per run, GHCRTS wide caliber, set on the pane by
-- the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-731.Probe731 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Term; con; var; Formula; _∈̇_; _≐_; _∧̇_; ⊤̇ )
open import FOL.Manipulation.Relativize using ( relativize; Δ₀-relativize )
import FOL.Absoluteness
open import Cubical.Data.Nat using ( ℕ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import V.Model {ℓ} using ( self∈sucV )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; 𝒟ₒ; 𝒟ₒ-intro; Lset-mono )
open import L.Axioms.Basic {ℓ} using ( LsetS; Lset-suc )
open import L.Ordinal {ℓ} using ( ω-ord; suc-ord )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Coding.EnvSet {ℓ} lem using ( envSet; envSet-out; Ix; envS )
open import L.Coding.Sat {ℓ} lem
  using ( tmIs; tmIs-var-in; tmIs-var-out; Sat; Sat-mem; cond
        ; cond∈-in; cond∈-out )

open import Cubical.Data.FinData using ( zero; suc; toℕ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( #_; sucV; ω )
open import Cubical.Functions.Logic using ( ⇔toPath )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- =====================================================================
-- SECTION 1.  THE c-TRACE REDUCTION, the machine-checked core of the
-- refutation.  For a carrier B and an ARBITRARY constant c (no
-- hypothesis places c anywhere), membership in
-- `Sat B (var zero IN con c)` at an environment z IS the fact that z's
-- slot-0 value lies in c, together with the slot identification.  Both
-- directions are one PT.rec over the landed readers cond∈-out /
-- cond∈-in, the term readers tmIs-var-out / tmIs-var-in, and the
-- definitional reading of the ≐ clause.  Generic in B and c (W2).
-- =====================================================================

module _ (B : S) (c : S) where

  v0 : Term S 1
  v0 = var zero

  c0 : Term S 1
  c0 = con c

  iz : Fin 3
  iz = zero

  i1 : Fin 3
  i1 = suc zero

  i2 : Fin 3
  i2 = suc (suc zero)

  tmIsV : Formula S 3
  tmIsV = tmIs v0 i1 i2

  tmIsC : Formula S 3
  tmIsC = tmIs c0 iz i2

  φc : Formula S 1
  φc = v0 ∈̇ con c

  cond-trace-equiv : (z : S)
    → ( (z ∷ []) ⊨ cond B φc )
    ≡ ( ∥ Σ[ v ∈ S ] (⟨ pr (# zero) (fst v) ∈ fst z ⟩ × ⟨ fst v ∈ fst c ⟩) ∥₁
      , squash₁ )
  cond-trace-equiv z = ⇔toPath fwd bwd
    where
    fwd : ⟨ (z ∷ []) ⊨ cond B φc ⟩
        → ∥ Σ[ v ∈ S ] (⟨ pr (# zero) (fst v) ∈ fst z ⟩ × ⟨ fst v ∈ fst c ⟩) ∥₁
    fwd h = PT.rec squash₁ step (cond∈-out B v0 (con c) z h)
      where
      step : Σ[ v ∈ S ] (Σ[ w ∈ S ]
               (⟨ (w ∷ v ∷ z ∷ []) ⊨ tmIsV ⟩
               × (⟨ (w ∷ v ∷ z ∷ []) ⊨ tmIsC ⟩
               × ⟨ fst v ∈ fst w ⟩)))
           → ∥ Σ[ v ∈ S ] (⟨ pr (# zero) (fst v) ∈ fst z ⟩ × ⟨ fst v ∈ fst c ⟩) ∥₁
      step (v , (w , (ht , (hu , r)))) =
        ∣ v , ( tmIs-var-out iz (w ∷ v ∷ z ∷ []) i1 i2 ht
              , subst (λ x → ⟨ fst v ∈ x ⟩) hu r ) ∣₁

    bwd : ∥ Σ[ v ∈ S ] (⟨ pr (# zero) (fst v) ∈ fst z ⟩ × ⟨ fst v ∈ fst c ⟩) ∥₁
        → ⟨ (z ∷ []) ⊨ cond B φc ⟩
    bwd = PT.rec squash₁ step
      where
      step : Σ[ v ∈ S ] (⟨ pr (# zero) (fst v) ∈ fst z ⟩ × ⟨ fst v ∈ fst c ⟩)
           → ⟨ (z ∷ []) ⊨ cond B φc ⟩
      step (v , (hv , hc)) =
        cond∈-in B v0 (con c) z
          ∣ v , ( c
                , ( tmIs-var-in iz (c ∷ v ∷ z ∷ []) i1 i2 hv
                  , ( refl , hc ) ) ) ∣₁

-- =====================================================================
-- SECTION 2.  THE REFUTATION SITE.  gamma = sucV omega, A = LsetS omega
-- omega-ord.  Both of the obligation's own hypotheses hold at this
-- site, and they are ALL the obligation carries: the type names no
-- placement fact for phi's constants.
-- =====================================================================

site-γ : V ℓ
site-γ = sucV ω

site-ordγ : IsOrd site-γ
site-ordγ = suc-ord ω-ord

site-ω∈γ : ⟨ ω ∈ site-γ ⟩
site-ω∈γ = self∈sucV ω

module DefAω = DefOf (Lset ω)

site-A : S
site-A = LsetS ω ω-ord

site-A∈ : ⟨ fst site-A ∈ Lset site-γ ⟩
site-A∈ = subst (λ w → ⟨ Lset ω ∈ w ⟩) (sym (Lset-suc ω))
  (𝒟ₒ-intro (Lset ω) (Lset ω) ∣ ⊤̇ , DefAω.defSet⊤≡A ∣₁)

-- =====================================================================
-- SECTION 3.  THE OBLIGATION'S TYPE.  STATED, NOT INHABITED.
--
-- Transcribed from agents/tasks/LJ-1-731/LJ-1.731.md.  The name is
-- exported at the file's top level as a TYPE;  no inhabitant stands
-- under it, no postulate supports it, and the file carries --safe.
-- review-of-Sat-in-carrier-stage.md states the refutation and the
-- corrected target.
-- =====================================================================

Sat-in-carrier-stage : Type (ℓ-suc ℓ)
Sat-in-carrier-stage =
    (γ : V ℓ) (oγ : IsOrd γ)
    → ⟨ ω ∈ γ ⟩
    → (A : S) → ⟨ fst A ∈ Lset γ ⟩
    → {n : ℕ} → (φ : Formula S n)
    → ⟨ Sat A φ ∈ˢ LsetS γ oγ ⟩

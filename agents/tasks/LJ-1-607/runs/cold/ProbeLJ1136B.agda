{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.136] Probe B.  Does [LJ-1.107]'s injection parameter DISCHARGE
-- when the injection is selected from L?
--
-- agents/reports/LJ-1-107/ProbeLJ1107A.agda:630 declares
--   module Chain (inj : (α : S) (oα : IsOrd α) (ω∈α : ...) (κ : S)
--                       (κ∈α : ...) → ⟪ α ⟫ ↪ ⟪ κ ⟫)
-- because LeastCard's witness is the truncation ∥ ⟪ κ ⟫ ≃ ⟪ α ⟫ ∥₁ and ↪
-- is not an hProp, so PT.rec refuses.  [LJ-1.114] then measured the
-- consequence: two independently chosen injections give colliding codes,
-- g₂' != g₁, so the induction cannot cohere.
--
--   Part 1.  pick-canonical: the <_L-least selection does not depend on
--            WHICH proof of non-emptiness reached it.  The term
--            [LJ-1.114] could not write.
--   Part 2.  discharge: a term of Chain's parameter shape, PRODUCED.
--   Part 3.  agree: the produced injection is canonical too.
--   Part 4.  C-38 guard.  The interface is instantiated at a concrete
--            non-degenerate graph, so nothing above is vacuous.
--
-- ABORT CRITERION, fixed in agents/reports/lj-1.136-report.md section 9.1
-- BEFORE this file was written:
--   GO      pick-canonical elaborates and Part 2 produces the parameter.
--   STOP    pick-canonical does not elaborate.
--   PARTIAL some step still demands an equivalence, so A5 carries CSB.
--
-- Untracked probe; ONE agda process under GHCRTS="-A64m -I0 -M8g";
-- never committed.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ1136B {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; Lset; Lset→isL; IsOrd )
open import L.Choice.Step {ℓ} lem using ( Mem; orderAt )
open import L.WellOrder.Base {ℓ-suc ℓ} using ( SWO; IsLeast; leastOf )
open import L.Coding.Model {ℓ} using ( svAt; domAt )
open import L.Axioms.Numerals {ℓ} using ( numeralL )

open import ProbeLJ1134A {ℓ} lem
  using ( injAt; module Small; module Concrete )

open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Foundations.HLevels using ( isPropΠ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

-- ---------------------------------------------------------------------
-- The selection, at a bound stage.  D is the domain set, C the range
-- set; both are PARAMETERS, so P-l is honoured and no type below names
-- a transparent presentation.
-- ---------------------------------------------------------------------

module Sel (β : V ℓ) (oβ : IsOrd β) (D C : S) where

  -- The crossing.  ONE LINE, as section 2.2 of the report measured it at
  -- the thirteen delivered sites.
  up : Mem (Lset β) → S
  up (x , m) = x , Lset→isL β oβ x m

  -- The range obligation.  [LJ-1.134] section 2.6 left it unpriced and
  -- OUTSIDE the selection.  It belongs INSIDE: put it in the predicate
  -- and the selected graph carries it, with no extra argument anywhere
  -- downstream.
  Ran : Mem (Lset β) → Type (ℓ-suc ℓ)
  Ran A = (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst (up A) ⟩ → ⟨ fst y ∈ fst C ⟩

  isPropRan : (A : Mem (Lset β)) → isProp (Ran A)
  isPropRan A = isPropΠ (λ x → isPropΠ (λ y → isPropΠ
                  (λ _ → snd (fst y ∈ fst C))))

  -- "A codes an injective function from D into C."  Every conjunct is
  -- Ω-valued, so leastOf takes the predicate with NO object-language
  -- work of its own: leastOf's predicate is an arbitrary metatheoretic
  -- hProp (src/L/WellOrder/Base.lagda.md:158-161).
  Good : Mem (Lset β) → Ω
  Good A = ((up A ∷ D ∷ []) ⊨ svAt zero)
         ⊓ (((up A ∷ D ∷ []) ⊨ domAt zero (suc zero))
         ⊓ (((up A ∷ D ∷ []) ⊨ injAt zero)
         ⊓  (Ran A , isPropRan A)))

  Ne : Type (ℓ-suc ℓ)
  Ne = ∥ Σ[ A ∈ Mem (Lset β) ] ⟨ Good A ⟩ ∥₁

  -- =====================================================================
  -- PART 1.  THE TERM [LJ-1.114] COULD NOT WRITE.
  -- =====================================================================

  pick : Ne → Mem (Lset β)
  pick h = fst (leastOf (orderAt β oβ) lem Good h)

  pick-good : (h : Ne) → ⟨ Good (pick h) ⟩
  pick-good h = fst (snd (leastOf (orderAt β oβ) lem Good h))

  -- The selection does not depend on WHICH proof of non-emptiness
  -- reached it: two branches of one induction, arguing differently,
  -- return the SAME graph.  This is what breaks g₂' != g₁.
  pick-canonical : (h₁ h₂ : Ne) → pick h₁ ≡ pick h₂
  pick-canonical h₁ h₂ =
    cong (λ z → fst (leastOf (orderAt β oβ) lem Good z)) (squash₁ h₁ h₂)

  -- =====================================================================
  -- PART 2.  THE DISCHARGE.
  -- SEALED, and the seal is not decoration.  Unsealed, this file
  -- exhausted an 8g heap twice: at 138.52 s with two Small applications,
  -- and at 98.42 s on the Part 3 instantiation.  orderAt is opaque for
  -- the same reason (src/L/Choice/Step.lagda.md:744).
  -- =====================================================================

  Data : Type (ℓ-suc ℓ)
  Data = Σ[ A ∈ Mem (Lset β) ] ⟨ Good A ⟩

  private
    module SmallOf (d : Data) =
      Small (up (fst d)) D C
        (fst (snd d)) (fst (snd (snd d)))
        (fst (snd (snd (snd d)))) (snd (snd (snd (snd d))))

  opaque
    injOf : Data → ⟪ fst D ⟫ → ⟪ fst C ⟫
    injOf d = SmallOf.small d

    injOf-inj : (d : Data) (m n : ⟪ fst D ⟫) → injOf d m ≡ injOf d n → m ≡ n
    injOf-inj d = SmallOf.small-inj d

  -- The deliverable: from the TRUNCATED existence of a constructible
  -- injective graph, an HONEST injection between the small index types.
  -- No module parameter, and no truncation left over.  This is the shape
  -- agents/reports/LJ-1-107/ProbeLJ1107A.agda:630 had to assume.
  discharge : Ne → Σ[ f ∈ (⟪ fst D ⟫ → ⟪ fst C ⟫) ]
                     ((m n : ⟪ fst D ⟫) → f m ≡ f n → m ≡ n)
  discharge h = injOf d , injOf-inj d
    where
    d : Data
    d = pick h , pick-good h

  -- =====================================================================
  -- PART 3.  THE PRODUCED INJECTION IS CANONICAL TOO.
  -- =====================================================================

  Data≡ : (d e : Data) → fst d ≡ fst e → d ≡ e
  Data≡ d e p = Σ≡Prop (λ A → snd (Good A)) p

  -- Stated GENERIC in the consumer.  With F abstract, `cong` cannot
  -- force the Small application; with F concrete and injOf UNSEALED the
  -- same statement exhausted the heap at 98.42 s.
  agree-generic : {ℓ' : Level} {X : Type ℓ'} (F : Data → X)
                → (h₁ h₂ : Ne)
                → F (pick h₁ , pick-good h₁) ≡ F (pick h₂ , pick-good h₂)
  agree-generic F h₁ h₂ = cong F (Data≡ _ _ (pick-canonical h₁ h₂))

  -- The instantiation the induction consumes.
  agree : (h₁ h₂ : Ne) → fst (discharge h₁) ≡ fst (discharge h₂)
  agree = agree-generic injOf

-- ---------------------------------------------------------------------
-- PART 4.  THE C-38 GUARD.
--
-- "A restatement that nothing can satisfy makes the module vacuously
-- true: it typechecks, it is fast, and it proves nothing."
-- dev/LESSONS.md:3427.  So the interface above is instantiated at
-- [LJ-1.134]'s concrete non-degenerate graph {<a,a>} with domain {a},
-- and the fourth conjunct, the range condition, is PROVED here.
-- ---------------------------------------------------------------------

module Witness (a : S) (β : V ℓ) (oβ : IsOrd β)
               (m : ⟨ fst (Concrete.G a) ∈ Lset β ⟩) where

  module Cc = Concrete a
  module Se = Sel β oβ Cc.Dm Cc.Dm

  A₀ : Mem (Lset β)
  A₀ = fst Cc.G , m

  up-A₀ : Se.up A₀ ≡ Cc.G
  up-A₀ = Σ≡Prop (λ z → snd (isL z)) refl

  -- The range condition: every value of the graph lands in the domain
  -- set, because every pair in it is <a,a>.
  ranG : (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst Cc.G ⟩
       → ⟨ fst y ∈ fst Cc.Dm ⟩
  ranG x y h = subst (λ w → ⟨ w ∈ fst Cc.Dm ⟩)
                 (sym (snd (Cc.split x y h))) Cc.inD

  good₀ : ⟨ Se.Good A₀ ⟩
  good₀ = subst
    (λ w → ⟨ ((w ∷ Cc.Dm ∷ []) ⊨ svAt zero)
          ⊓ (((w ∷ Cc.Dm ∷ []) ⊨ domAt zero (suc zero))
          ⊓ (((w ∷ Cc.Dm ∷ []) ⊨ injAt zero)
          ⊓  (Se.Ran A₀ , Se.isPropRan A₀))) ⟩)
    (sym up-A₀)
    (Cc.sv , (Cc.dm , (Cc.ij , λ x y h →
       ranG x y (subst (λ w → ⟨ pr (fst x) (fst y) ∈ fst w ⟩) up-A₀ h))))

  -- The interface is INHABITED.  Nothing above is vacuous.
  ne : Se.Ne
  ne = ∣ A₀ , good₀ ∣₁

  -- And the composite runs: an honest injection, with no hypothesis
  -- beyond the graph lying in the stage.
  theInjection : ⟪ fst Cc.Dm ⟫ → ⟪ fst Cc.Dm ⟫
  theInjection = fst (Se.discharge ne)

  theInjection-inj : (u v : ⟪ fst Cc.Dm ⟫)
                   → theInjection u ≡ theInjection v → u ≡ v
  theInjection-inj = snd (Se.discharge ne)

-- A fully concrete instance, at the numeral zero.
module WitnessZero = Witness (numeralL 0)

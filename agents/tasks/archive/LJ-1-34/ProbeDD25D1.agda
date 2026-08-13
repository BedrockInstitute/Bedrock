{-# OPTIONS --cubical --safe --guardedness #-}

-- [DD25 review of LJ-1.34] THE GENERIC LEAF LAYER.
--
-- The return `_build/lj-1.34-report.md` measured 0.436 s per line and
-- named an unmeasured cure in its section 6: a generic leaf layer with
-- the body abstract, the way [LJ-1.33-R] did the outer layer.  It
-- declined to price it under P-l.  This probe BUILDS it and MEASURES it.
--
-- The experiment.  The endpoint statements `StepAgree.step-out` and
-- `StepAgree.step-in` are TEXTUALLY IDENTICAL to the return's
-- (src/ProbeLJ134.agda:275-287): the same hypotheses, the delivered
-- `StepAt` on one side and the story's `StepStory.StepBndB` on the
-- other.  The only change is the INTERIOR: every agreement lemma is
-- generic in the leaf body ψ, and the built `DefBody` enters once, at
-- the instantiation.
--
-- If the cost is the elaborator unfolding the built `DefBody` per use,
-- the generic interior costs nothing and the instantiation pays once.
-- If the cost is intrinsic to naming the built satisfaction in the
-- endpoint type, the instantiation pays it all and nothing is saved.
--
-- Untracked probe; one Agda process under GHCRTS="-A64m -I0 -M8g";
-- never committed; thrown away per D-1.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeDD25D1 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; var; _∈̇_; _∧̇_; _⇒̇_; ∃̇_; ∀̇_; ∃̇∈ )
open import FOL.LevyHierarchy using ( Δ₀; δ-∃∈ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; 𝒟ₒ )
open import L.Coding.Model {ℓ}
  using ( appAt; extAt; extAt-out; extAt-in; extAt-in-both )
open import L.Coding.Powerset {ℓ} lem
  using ( DefAt; DefBody )
open import L.Coding.Sequence {ℓ} lem
  using ( StepAt; StepBody )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

-- =====================================================================
-- SECTION 1: THE STORY.  Unchanged from src/ProbeLJ134.agda:66-99.
-- =====================================================================

DefAtB : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
DefAtB u w K = extAt u (∃̇∈ (var (suc K)) (∃̇∈ (var (suc (suc K))) (DefBody w)))

module StepStory {n : ℕ} (v b f : Fin n) where
  private
    K V₁ B₁ F₁ : Fin (suc n)
    K  = zero
    V₁ = suc v
    B₁ = suc b
    F₁ = suc f

  BodyB : Formula S (5 + n)
  BodyB =
    (var (suc (suc zero)) ∈̇ var (suc (suc (suc (suc B₁)))))
    ∧̇ ( appAt (suc (suc (suc (suc F₁)))) (suc (suc zero)) (suc zero)
      ∧̇ ( DefAtB zero (suc zero) (suc (suc (suc (suc zero))))
        ∧̇ (var (suc (suc (suc zero))) ∈̇ var zero) ) )

  StepWitB : Formula S (suc (suc n))
  StepWitB =
    ∃̇∈ (var (suc (suc b)))
      (∃̇∈ (var (suc (suc K)))
        (∃̇∈ (var (suc (suc (suc K))))
          BodyB))

  StepBndB : Formula S (suc n)
  StepBndB = extAt V₁ StepWitB

-- =====================================================================
-- SECTION 2: THE TEMPLATE CERTIFICATE.  Unchanged from
-- src/ProbeLJ134.agda:111-129, so the totals compare.
-- =====================================================================
module WitCert {n : ℕ} (v b f : Fin n) where
  private
    K : Fin (suc n)
    K = zero

  Δ₀-wit-tmpl : (φ : Formula S (5 + n)) → Δ₀ φ
              → Δ₀ (∃̇∈ (var (suc (suc b)))
                      (∃̇∈ (var (suc (suc K)))
                        (∃̇∈ (var (suc (suc (suc K))))
                          φ)))
  Δ₀-wit-tmpl φ d = δ-∃∈ (δ-∃∈ (δ-∃∈ d))

  Δ₀-wit : Δ₀ (StepStory.BodyB v b f)
         → Δ₀ (StepStory.StepWitB v b f)
  Δ₀-wit d = Δ₀-wit-tmpl (StepStory.BodyB v b f) d

-- =====================================================================
-- SECTION 3: THE GENERIC LAYER.  ψ is the leaf body, a VARIABLE.
-- Nothing in this section names the built `DefBody`.
-- =====================================================================
module G {n : ℕ} (ψ : Formula S (suc (suc (suc (5 + n))))) (v b f : Fin n)
  where
  private
    K V₁ B₁ F₁ : Fin (suc n)
    K  = zero
    V₁ = suc v
    B₁ = suc b
    F₁ = suc f

    KB : Fin (5 + n)
    KB = suc (suc (suc (suc zero)))

  -- The delivered leaf shape and the bounded leaf shape, generic in ψ.
  LeafD : Formula S (5 + n)
  LeafD = extAt zero (∃̇ (∃̇ ψ))

  LeafB : Formula S (5 + n)
  LeafB = extAt zero (∃̇∈ (var (suc KB)) (∃̇∈ (var (suc (suc KB))) ψ))

  BodyD : Formula S (5 + n)
  BodyD =
    (var (suc (suc zero)) ∈̇ var (suc (suc (suc (suc B₁)))))
    ∧̇ ( appAt (suc (suc (suc (suc F₁)))) (suc (suc zero)) (suc zero)
      ∧̇ ( LeafD ∧̇ (var (suc (suc (suc zero))) ∈̇ var zero) ) )

  BodyB : Formula S (5 + n)
  BodyB =
    (var (suc (suc zero)) ∈̇ var (suc (suc (suc (suc B₁)))))
    ∧̇ ( appAt (suc (suc (suc (suc F₁)))) (suc (suc zero)) (suc zero)
      ∧̇ ( LeafB ∧̇ (var (suc (suc (suc zero))) ∈̇ var zero) ) )

  WitD : Formula S (suc (suc n))
  WitD = ∃̇ (∃̇ (∃̇ BodyD))

  WitB : Formula S (suc (suc n))
  WitB =
    ∃̇∈ (var (suc (suc b)))
      (∃̇∈ (var (suc (suc K)))
        (∃̇∈ (var (suc (suc (suc K))))
          BodyB))

  ClauseD : Formula S (suc n)
  ClauseD = extAt V₁ WitD

  ClauseB : Formula S (suc n)
  ClauseB = extAt V₁ WitB

  LeafBndG : S ^ (5 + n) → Type (ℓ-suc ℓ)
  LeafBndG δ = (c' v' : S) → (x : S)
             → ⟨ (v' ∷ c' ∷ x ∷ δ) ⊨ ψ ⟩
             → ⟨ fst c' ∈ fst (lookup KB δ) ⟩
             × ⟨ fst v' ∈ fst (lookup KB δ) ⟩

  module LeafAgreeG (δ : S ^ (5 + n)) where
    private
      ΦB : Formula S (suc (5 + n))
      ΦB = ∃̇∈ (var (suc KB)) (∃̇∈ (var (suc (suc KB))) ψ)

      Φ : Formula S (suc (5 + n))
      Φ = ∃̇ (∃̇ ψ)

      drop : (x : S) → ⟨ (x ∷ δ) ⊨ ΦB ⟩ → ⟨ (x ∷ δ) ⊨ Φ ⟩
      drop x = PT.map (λ { (c' , (_ , h₁)) →
        c' , PT.map (λ { (v' , (_ , h₂)) → v' , h₂ }) h₁ })

      add : (x : S) → LeafBndG δ → ⟨ (x ∷ δ) ⊨ Φ ⟩ → ⟨ (x ∷ δ) ⊨ ΦB ⟩
      add x bnd = PT.rec (snd ((x ∷ δ) ⊨ ΦB))
        (λ { (c' , h₁) → PT.rec (snd ((x ∷ δ) ⊨ ΦB))
          (λ { (v' , h₂) →
            let b = bnd c' v' x h₂
            in ∣ c' , (b .fst , ∣ v' , (b .snd , h₂) ∣₁) ∣₁ }) h₁ })

    leaf-out : LeafBndG δ → ⟨ δ ⊨ LeafB ⟩ → ⟨ δ ⊨ LeafD ⟩
    leaf-out bnd h = extAt-in-both zero Φ δ
      (λ x x∈ → drop x (extAt-out zero ΦB δ h x x∈))
      (λ x hu → extAt-in zero ΦB δ h x (add x bnd hu))

    leaf-in : LeafBndG δ → ⟨ δ ⊨ LeafD ⟩ → ⟨ δ ⊨ LeafB ⟩
    leaf-in bnd h = extAt-in-both zero ΦB δ
      (λ x x∈ → add x bnd (extAt-out zero Φ δ h x x∈))
      (λ x hw → extAt-in zero Φ δ h x (drop x hw))

  module BodyAgreeG (δ : S ^ (5 + n)) where
    open LeafAgreeG δ

    body-out : LeafBndG δ → ⟨ δ ⊨ BodyB ⟩ → ⟨ δ ⊨ BodyD ⟩
    body-out bnd h =
      ( h .fst
      , ( h .snd .fst
        , ( leaf-out bnd (h .snd .snd .fst)
          , h .snd .snd .snd ) ) )

    body-in : LeafBndG δ → ⟨ δ ⊨ BodyD ⟩ → ⟨ δ ⊨ BodyB ⟩
    body-in bnd h =
      ( h .fst
      , ( h .snd .fst
        , ( leaf-in bnd (h .snd .snd .fst)
          , h .snd .snd .snd ) ) )

  module StepAgreeG (γ : S ^ suc n) where
    OuterBndG : (z : S) → Type (ℓ-suc ℓ)
    OuterBndG z =
        (c w d : S) → ⟨ (d ∷ w ∷ c ∷ z ∷ γ) ⊨ BodyD ⟩
                    → ⟨ fst c ∈ fst (lookup B₁ γ) ⟩
                    × ( ⟨ fst w ∈ fst (lookup K γ) ⟩
                      × ⟨ fst d ∈ fst (lookup K γ) ⟩ )

    LeafFactsG : (z : S) → Type (ℓ-suc ℓ)
    LeafFactsG z = (c w d : S) → LeafBndG (d ∷ w ∷ c ∷ z ∷ γ)

    body-in-lemma : (z c w d : S) → LeafBndG (d ∷ w ∷ c ∷ z ∷ γ)
                  → ⟨ (d ∷ w ∷ c ∷ z ∷ γ) ⊨ BodyD ⟩
                  → ⟨ (d ∷ w ∷ c ∷ z ∷ γ) ⊨ BodyB ⟩
    body-in-lemma z c w d bnd = BodyAgreeG.body-in (d ∷ w ∷ c ∷ z ∷ γ) bnd

    body-out-lemma : (z c w d : S) → LeafBndG (d ∷ w ∷ c ∷ z ∷ γ)
                   → ⟨ (d ∷ w ∷ c ∷ z ∷ γ) ⊨ BodyB ⟩
                   → ⟨ (d ∷ w ∷ c ∷ z ∷ γ) ⊨ BodyD ⟩
    body-out-lemma z c w d bnd = BodyAgreeG.body-out (d ∷ w ∷ c ∷ z ∷ γ) bnd

    wit-out : (z : S) → LeafFactsG z
            → ⟨ (z ∷ γ) ⊨ WitB ⟩ → ⟨ (z ∷ γ) ⊨ WitD ⟩
    wit-out z lf = PT.rec (snd ((z ∷ γ) ⊨ WitD))
      (λ { (c₀ , (_ , h₁)) → PT.rec (snd ((z ∷ γ) ⊨ WitD))
        (λ { (w₀ , (_ , h₂)) → PT.rec (snd ((z ∷ γ) ⊨ WitD))
          (λ { (d₀ , (_ , hb)) →
            ∣ c₀ , ∣ w₀ , ∣ d₀ , body-out-lemma z c₀ w₀ d₀ (lf c₀ w₀ d₀) hb
                    ∣₁ ∣₁ ∣₁ }) h₂ }) h₁ })

    wit-in : (z : S) → OuterBndG z → LeafFactsG z
           → ⟨ (z ∷ γ) ⊨ WitD ⟩ → ⟨ (z ∷ γ) ⊨ WitB ⟩
    wit-in z ob lf = PT.rec (snd ((z ∷ γ) ⊨ WitB))
      (λ { (c₀ , h₁) → PT.rec (snd ((z ∷ γ) ⊨ WitB))
        (λ { (w₀ , h₂) → PT.rec (snd ((z ∷ γ) ⊨ WitB))
          (λ { (d₀ , hb) →
            let b = ob c₀ w₀ d₀ hb
            in ∣ c₀ , ( b .fst
                      , ∣ w₀ , ( b .snd .fst
                              , ∣ d₀ , ( b .snd .snd
                                      , body-in-lemma z c₀ w₀ d₀ (lf c₀ w₀ d₀) hb ) ∣₁ ) ∣₁ ) ∣₁ })
            h₂ }) h₁ })

    step-out : ((z : S) → OuterBndG z) → ((z : S) → LeafFactsG z)
             → ⟨ γ ⊨ ClauseD ⟩ → ⟨ γ ⊨ ClauseB ⟩
    step-out ob lf h = extAt-in-both V₁ WitB γ
      (λ z z∈ → wit-in z (ob z) (lf z) (extAt-out V₁ WitD γ h z z∈))
      (λ z hw → extAt-in V₁ WitD γ h z (wit-out z (lf z) hw))

    step-in : ((z : S) → OuterBndG z) → ((z : S) → LeafFactsG z)
            → ⟨ γ ⊨ ClauseB ⟩ → ⟨ γ ⊨ ClauseD ⟩
    step-in ob lf h = extAt-in-both V₁ WitD γ
      (λ z z∈ → wit-out z (lf z) (extAt-out V₁ WitB γ h z z∈))
      (λ z hu → extAt-in V₁ WitB γ h z (wit-in z (ob z) (lf z) hu))

-- =====================================================================
-- SECTION 4: THE INSTANTIATION.  The built `DefBody` enters HERE and
-- nowhere else.  The endpoint types below are textually the return's
-- (src/ProbeLJ134.agda:146-150, :229-238, :275-287).
-- =====================================================================

LeafBnd : {n : ℕ} → S ^ (5 + n) → Type (ℓ-suc ℓ)
LeafBnd {n} δ = (c' v' : S) → (x : S)
              → ⟨ (v' ∷ c' ∷ x ∷ δ) ⊨ DefBody (suc zero) ⟩
              → ⟨ fst c' ∈ fst (lookup (suc (suc (suc (suc zero)))) δ) ⟩
              × ⟨ fst v' ∈ fst (lookup (suc (suc (suc (suc zero)))) δ) ⟩

module StepAgree {n : ℕ} (v b f : Fin n) (γ : S ^ suc n) where
  private
    K V₁ B₁ F₁ : Fin (suc n)
    K  = zero
    V₁ = suc v
    B₁ = suc b
    F₁ = suc f

  Φ : Formula S (suc (suc n))
  Φ = ∃̇ (∃̇ (∃̇ (StepBody B₁ F₁)))

  OuterBnd : (z : S) → Type (ℓ-suc ℓ)
  OuterBnd z =
      (c w d : S) → ⟨ (d ∷ w ∷ c ∷ z ∷ γ) ⊨ StepBody B₁ F₁ ⟩
                  → ⟨ fst c ∈ fst (lookup B₁ γ) ⟩
                  × ( ⟨ fst w ∈ fst (lookup K γ) ⟩
                    × ⟨ fst d ∈ fst (lookup K γ) ⟩ )

  LeafFacts : (z : S) → Type (ℓ-suc ℓ)
  LeafFacts z = (c w d : S) → LeafBnd {n} (d ∷ w ∷ c ∷ z ∷ γ)

  private
    module GS = G.StepAgreeG {n} (DefBody (suc zero)) v b f γ

  -- OUT: the delivered machine step satisfies the bounded story.
  step-out : ((z : S) → OuterBnd z) → ((z : S) → LeafFacts z)
           → ⟨ γ ⊨ StepAt V₁ B₁ F₁ ⟩ → ⟨ γ ⊨ StepStory.StepBndB v b f ⟩
  step-out = GS.step-out

  -- IN: the bounded story assembles the delivered machine step.
  step-in : ((z : S) → OuterBnd z) → ((z : S) → LeafFacts z)
          → ⟨ γ ⊨ StepStory.StepBndB v b f ⟩ → ⟨ γ ⊨ StepAt V₁ B₁ F₁ ⟩
  step-in = GS.step-in

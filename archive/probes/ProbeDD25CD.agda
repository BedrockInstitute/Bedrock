{-# OPTIONS --cubical --safe --guardedness #-}

-- [DD25 review of LJ-1.33] The shared machine-reading layer.
--
-- The claim under test: leg D's decode does NOT have to name the built
-- machine body in any type.  The delivered clause and the bounded story
-- clause carry THE SAME body formula; they differ only by three bounds.
-- So the agreement is a bound-drop and a bound-add over an ABSTRACT body
-- formula, stated once, then instantiated.
--
-- Section 1 is the template layer, generic in the body.  Section 2 is the
-- story clause, verbatim from src/ProbeLJ133.agda:59-96.  Section 3 is the
-- instantiation: the agreement between the bounded story clause and the
-- DELIVERED StepAt, both directions, proved by the layer alone.
--
-- Untracked probe; one Agda process under GHCRTS="-A64m -I0 -M8g"; never
-- committed; thrown away per D-1.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeDD25CD {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; var; _∈̇_; _∧̇_; _⇒̇_; ∃̇_; ∀̇_; ∃̇∈ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; 𝒟ₒ )
open import L.Coding.Model {ℓ}
  using ( appAt; appAt-adequate; extAt; extAt-out; extAt-in; extAt-in-both )
open import L.Coding.Powerset {ℓ} lem
  using ( DefAt; DefAt-in; DefAt-out; DefOK )
open import L.Coding.Sequence {ℓ} lem
  using ( StepAt; StepBody; Records; StepOf; PowOK )
open import L.Condensation {ℓ} lem
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

-- =====================================================================
-- SECTION 1: THE TEMPLATE LAYER.  Generic in the body formula φ.
-- Nothing here mentions StepBody, DefAt, appAt or any built formula.
-- =====================================================================
module Triple {n : ℕ} (Bs Ks : Fin (suc n)) (φ : Formula S (5 + n))
              (γ : S ^ suc n) where

  -- The bounded witness: three bounded existentials over the body.
  Wit : Formula S (suc (suc n))
  Wit = ∃̇∈ (var (suc Bs))
          (∃̇∈ (var (suc (suc Ks)))
            (∃̇∈ (var (suc (suc (suc Ks))))
              φ))

  -- The unbounded witness: three plain existentials over the same body.
  Unb : Formula S (suc (suc n))
  Unb = ∃̇ (∃̇ (∃̇ φ))

  -- The bound hypothesis, stated on the abstract body.
  Bounds : S → Type (ℓ-suc ℓ)
  Bounds z = (c w d : S) → ⟨ (d ∷ w ∷ c ∷ z ∷ γ) ⊨ φ ⟩
           → ⟨ fst c ∈ fst (lookup Bs γ) ⟩
           × ( ⟨ fst w ∈ fst (lookup Ks γ) ⟩
             × ⟨ fst d ∈ fst (lookup Ks γ) ⟩ )

  -- Drop the bounds.
  drop : (z : S) → ⟨ (z ∷ γ) ⊨ Wit ⟩ → ⟨ (z ∷ γ) ⊨ Unb ⟩
  drop z = PT.rec (snd ((z ∷ γ) ⊨ Unb)) (λ { (c , (_ , h₁)) →
    PT.rec (snd ((z ∷ γ) ⊨ Unb)) (λ { (w , (_ , h₂)) →
      PT.rec (snd ((z ∷ γ) ⊨ Unb)) (λ { (d , (_ , hb)) →
        ∣ c , ∣ w , ∣ d , hb ∣₁ ∣₁ ∣₁ }) h₂ }) h₁ })

  -- Add the bounds.
  add : (z : S) → Bounds z → ⟨ (z ∷ γ) ⊨ Unb ⟩ → ⟨ (z ∷ γ) ⊨ Wit ⟩
  add z bnd = PT.rec (snd ((z ∷ γ) ⊨ Wit)) (λ { (c , h₁) →
    PT.rec (snd ((z ∷ γ) ⊨ Wit)) (λ { (w , h₂) →
      PT.rec (snd ((z ∷ γ) ⊨ Wit)) (λ { (d , hb) →
        ∣ c , ( bnd c w d hb .fst
              , ∣ w , ( bnd c w d hb .snd .fst
                      , ∣ d , (bnd c w d hb .snd .snd , hb) ∣₁ ) ∣₁ ) ∣₁ })
          h₂ }) h₁ })

  -- The clause-level agreement: one extAt over each witness.
  toUnb : (y : Fin (suc n)) → ((z : S) → Bounds z)
        → ⟨ γ ⊨ extAt y Wit ⟩ → ⟨ γ ⊨ extAt y Unb ⟩
  toUnb y bnd h = extAt-in-both y Unb γ
    (λ z z∈ → drop z (extAt-out y Wit γ h z z∈))
    (λ z hu → extAt-in y Wit γ h z (add z (bnd z) hu))

  toWit : (y : Fin (suc n)) → ((z : S) → Bounds z)
        → ⟨ γ ⊨ extAt y Unb ⟩ → ⟨ γ ⊨ extAt y Wit ⟩
  toWit y bnd h = extAt-in-both y Wit γ
    (λ z z∈ → add z (bnd z) (extAt-out y Unb γ h z z∈))
    (λ z hw → extAt-in y Unb γ h z (drop z hw))

-- =====================================================================
-- SECTION 2: THE STORY'S STEP CLAUSE.  Verbatim from the return's probe
-- (src/ProbeLJ133.agda:59-96), so the target is the same target.
-- =====================================================================
module StepStory {n : ℕ} (K : Fin (suc n)) (v b f : Fin n) where
  private
    V₁ B₁ F₁ : Fin (suc n)
    V₁ = suc v
    B₁ = suc b
    F₁ = suc f

  -- THE ONE CHANGE against ProbeDD25CL: the story's body is the
  -- DELIVERED body, not a hand-written copy of it.  The two are the same
  -- formula (src/ProbeLJ133.agda:70-76 against
  -- src/L/Coding/Sequence.lagda.md:113-117), so this changes no
  -- mathematics.  It removes one conversion.
  Body : Formula S (5 + n)
  Body = StepBody B₁ F₁

  StepWit : Formula S (suc (suc n))
  StepWit =
    ∃̇∈ (var (suc (suc b)))
      (∃̇∈ (var (suc (suc K)))
        (∃̇∈ (var (suc (suc (suc K))))
          Body))

  StepIn : Formula S (suc n)
  StepIn = ∀̇ ((var zero ∈̇ var (suc (suc v))) ⇒̇ StepWit)

  StepOut : Formula S (suc n)
  StepOut = ∀̇ (StepWit ⇒̇ (var zero ∈̇ var (suc (suc v))))

  StepBnd : Formula S (suc n)
  StepBnd = StepIn ∧̇ StepOut

-- =====================================================================
-- SECTION 3: THE INSTANTIATION.  The agreement between the bounded story
-- clause and the DELIVERED StepAt, both directions.  The bound facts are
-- a hypothesis, exactly as they are in the return's probe.
-- =====================================================================
module StepAgree {n : ℕ} (K : Fin (suc n)) (v b f : Fin n) (γ : S ^ suc n) where
  private
    V₁ B₁ F₁ : Fin (suc n)
    V₁ = suc v
    B₁ = suc b
    F₁ = suc f

  open Triple B₁ K (StepBody B₁ F₁) γ public

  -- OUT: the delivered machine step satisfies the bounded story.
  step-out : ((z : S) → Bounds z)
           → ⟨ γ ⊨ StepAt V₁ B₁ F₁ ⟩ → ⟨ γ ⊨ StepStory.StepBnd K v b f ⟩
  step-out bnd h = toWit V₁ bnd h

  -- IN: the bounded story assembles the delivered machine step.
  step-in : ((z : S) → Bounds z)
          → ⟨ γ ⊨ StepStory.StepBnd K v b f ⟩ → ⟨ γ ⊨ StepAt V₁ B₁ F₁ ⟩
  step-in bnd h = toUnb V₁ bnd h

  -- ===================================================================
  -- THE DISCHARGE.  The return's probe states the bound facts on the
  -- machine's clean content type (Records).  Here that hypothesis is
  -- converted into the layer's generic one, so the two probes prove the
  -- SAME theorem from the SAME hypotheses.  This is the only place where
  -- the built body is read, and it reads it ONCE.
  -- (src/ProbeLJ133.agda:123-126 for BoundOK; the reading mirrors the
  -- delivered readBody at src/L/Coding/Sequence.lagda.md:170-182.)
  -- ===================================================================
  BoundOK : Type (ℓ-suc ℓ)
  BoundOK =
      ((c w : S) → Records B₁ F₁ γ c w → ⟨ fst w ∈ fst (lookup K γ) ⟩)
    × ((c w : S) → Records B₁ F₁ γ c w → ⟨ 𝒟ₒ (fst w) ∈ fst (lookup K γ) ⟩)

  discharge : PowOK B₁ F₁ γ → BoundOK → (z : S) → Bounds z
  discharge ok (bw , bd) z c w d body =
    ( body .fst
    , ( bw c w rec
      , subst (λ X → ⟨ X ∈ fst (lookup K γ) ⟩) (sym qd) (bd c w rec) ) )
    where
    rec : Records B₁ F₁ γ c w
    rec = body .fst
        , subst ⟨_⟩ (appAt-adequate (suc (suc (suc (suc (suc f)))))
                                    (suc (suc zero)) (suc zero)
                                    (d ∷ w ∷ c ∷ z ∷ γ))
            (body .snd .fst)

    qd : fst d ≡ 𝒟ₒ (fst w)
    qd = DefAt-out w zero (suc zero) (d ∷ w ∷ c ∷ z ∷ γ)
           (λ x x∈ → isL-trans {x = 𝒟ₒ (fst w)} {y = x} x∈ (ok c w rec))
           refl (body .snd .snd .fst)

  -- The return's own two signatures, proved through the layer.
  step-out' : ⟨ γ ⊨ StepAt V₁ B₁ F₁ ⟩ → PowOK B₁ F₁ γ → BoundOK
            → ⟨ γ ⊨ StepStory.StepBnd K v b f ⟩
  step-out' h ok bo = step-out (discharge ok bo) h

  step-in' : ⟨ γ ⊨ StepStory.StepBnd K v b f ⟩ → PowOK B₁ F₁ γ → BoundOK
           → ⟨ γ ⊨ StepAt V₁ B₁ F₁ ⟩
  step-in' h ok bo = step-in (discharge ok bo) h

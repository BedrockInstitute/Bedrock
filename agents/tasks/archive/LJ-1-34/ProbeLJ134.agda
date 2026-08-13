{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.34] The certificate story against the delivered machine.
--
-- The claim under test: leg D's story clause with its DefAt leaf BOUNDED
-- (the code and value existentials of the definable-powerset description
-- bounded by the story's bound), carrying its Delta-0 certificate,
-- decoded against the delivered machine.
--
-- Section 1: the bounded story's step clause.  The DefAt leaf becomes
-- DefAtB: the same description with the two existentials bounded by K.
-- The leaf content is the DELIVERED DefBody
-- (src/L/Coding/Powerset.lagda.md:436-440).
-- Section 2: the Delta-0 certificate.  The witness shape's certificate
-- is TEMPLATE: generic in the body.  The concrete body's certificate
-- needs the leaf content's certificate, which does not exist (the leaves
-- carry unbounded quantifiers).  The failing concrete certificates are
-- in src/ProbeLJ134Cert.agda.
-- Section 3: the decode against the delivered machine, both directions,
-- through the formula readings, with the five bound facts as
-- hypotheses: c in B, w in K, d in K, and the code and value of the
-- bounded DefAt leaf in K.
--
-- Untracked probe; one Agda process under GHCRTS="-A64m -I0 -M8g"; never
-- committed; thrown away per D-1.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ134 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

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
-- SECTION 1: THE BOUNDED STORY'S STEP CLAUSE.
-- =====================================================================

-- The bounded definable-powerset description.  The code existential
-- (var 1 of DefBody) and the value existential (var 0 of DefBody) are
-- bounded by the bound slot K.
DefAtB : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
DefAtB u w K = extAt u (∃̇∈ (var (suc K)) (∃̇∈ (var (suc (suc K))) (DefBody w)))

-- The bounded story's step clause, at the story's arity suc n, with the
-- bound K at slot zero of the environment.  Same shape as the return's
-- StepBnd (src/ProbeLJ133.agda:80-96) and ProbeDD25CD's StepStory; the
-- one change is the bounded DefAt leaf inside the body.
module StepStory {n : ℕ} (v b f : Fin n) where
  private
    K V₁ B₁ F₁ : Fin (suc n)
    K  = zero
    V₁ = suc v
    B₁ = suc b
    F₁ = suc f

  -- The bounded body.  K is at var (suc (suc (suc (suc zero)))) in the
  -- body (the first slot of the story's environment, shifted past the
  -- four body variables d w c z).
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
-- SECTION 2: THE DELTA-0 CERTIFICATE, TEMPLATE HALF.
--
-- The witness shape's certificate is template: it closes for ANY body
-- with a Delta-0 certificate.  The concrete body's certificate needs
-- the leaf content's certificate, which does not exist: the delivered
-- leaves (isCodeAt, satGraphAt, DefinesAt) carry unbounded quantifiers
-- (src/L/Coding/Powerset.lagda.md:297-298, :191-192, :217-219).  The
-- failing concrete certificates are in src/ProbeLJ134Cert.agda.
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

  -- The concrete witness certificate, stated as the missing premise.
  -- The premise Δ₀ (StepStory.BodyB v b f) is exactly the bounded
  -- satisfaction substrate: it needs Delta-0 witnesses for the code
  -- description, the table, and the defines relation.
  Δ₀-wit : Δ₀ (StepStory.BodyB v b f)
         → Δ₀ (StepStory.StepWitB v b f)
  Δ₀-wit d = Δ₀-wit-tmpl (StepStory.BodyB v b f) d

-- =====================================================================
-- SECTION 3: THE DECODE AGAINST THE DELIVERED MACHINE.
--
-- Both directions, through the formula readings (extAt-out, extAt-in,
-- extAt-in-both).  The leaf agreement is pure bound-add / bound-drop at
-- the two DefAt existentials: the leaf CONTENT is the delivered DefBody,
-- so the proof never pattern-matches the content.  The TYPES name the
-- built DefAt satisfaction, and the elaborator unfolds the built tree
-- while checking them.  That unfolding is the measured cost (the
-- profile: LeafAgree.leaf-in and leaf-out at about 21 seconds each).
-- =====================================================================

-- The bound facts for the bounded leaf, at a body environment δ
-- (d ∷ w ∷ c ∷ z ∷ γ): the code and the value of the description lie in
-- K = δ at index 4.
LeafBnd : {n : ℕ} → S ^ (5 + n) → Type (ℓ-suc ℓ)
LeafBnd {n} δ = (c' v' : S) → (x : S)
              → ⟨ (v' ∷ c' ∷ x ∷ δ) ⊨ DefBody (suc zero) ⟩
              → ⟨ fst c' ∈ fst (lookup (suc (suc (suc (suc zero)))) δ) ⟩
              × ⟨ fst v' ∈ fst (lookup (suc (suc (suc (suc zero)))) δ) ⟩

-- The leaf agreement at the body context.  The leaf CONTENT is the same
-- delivered DefBody on both sides; only the two existentials differ.
module LeafAgree {n : ℕ} (δ : S ^ (5 + n)) where
  private
    K : Fin (5 + n)
    K = suc (suc (suc (suc zero)))

    ΦB : Formula S (suc (5 + n))
    ΦB = ∃̇∈ (var (suc K)) (∃̇∈ (var (suc (suc K))) (DefBody (suc zero)))

    Φ : Formula S (suc (5 + n))
    Φ = ∃̇ (∃̇ (DefBody (suc zero)))

    drop : (x : S) → ⟨ (x ∷ δ) ⊨ ΦB ⟩ → ⟨ (x ∷ δ) ⊨ Φ ⟩
    drop x = PT.map (λ { (c' , (_ , h₁)) →
      c' , PT.map (λ { (v' , (_ , h₂)) → v' , h₂ }) h₁ })

    add : (x : S) → LeafBnd δ → ⟨ (x ∷ δ) ⊨ Φ ⟩ → ⟨ (x ∷ δ) ⊨ ΦB ⟩
    add x bnd = PT.rec (snd ((x ∷ δ) ⊨ ΦB))
      (λ { (c' , h₁) → PT.rec (snd ((x ∷ δ) ⊨ ΦB))
        (λ { (v' , h₂) →
          let b = bnd c' v' x h₂
          in ∣ c' , (b .fst , ∣ v' , (b .snd , h₂) ∣₁) ∣₁ }) h₁ })

  -- OUT: the bounded leaf reads into the delivered leaf.
  leaf-out : LeafBnd δ → ⟨ δ ⊨ DefAtB zero (suc zero) K ⟩ → ⟨ δ ⊨ DefAt zero (suc zero) ⟩
  leaf-out bnd h = extAt-in-both zero Φ δ
    (λ x x∈ → drop x (extAt-out zero ΦB δ h x x∈))
    (λ x hu → extAt-in zero ΦB δ h x (add x bnd hu))

  -- IN: the delivered leaf assembles the bounded leaf.
  leaf-in : LeafBnd δ → ⟨ δ ⊨ DefAt zero (suc zero) ⟩ → ⟨ δ ⊨ DefAtB zero (suc zero) K ⟩
  leaf-in bnd h = extAt-in-both zero ΦB δ
    (λ x x∈ → add x bnd (extAt-out zero Φ δ h x x∈))
    (λ x hw → extAt-in zero Φ δ h x (drop x hw))

-- The body agreement: the bounded body reads into the delivered body and
-- back, through the leaf agreement and the four conjuncts.
module BodyAgree {n : ℕ} (v b f : Fin n) (δ : S ^ (5 + n)) where
  private
    B₁ F₁ : Fin (suc n)
    B₁ = suc b
    F₁ = suc f

  open LeafAgree δ

  body-out : LeafBnd δ
           → ⟨ δ ⊨ StepStory.BodyB v b f ⟩ → ⟨ δ ⊨ StepBody B₁ F₁ ⟩
  body-out bnd h =
    ( h .fst
    , ( h .snd .fst
      , ( leaf-out bnd (h .snd .snd .fst)
        , h .snd .snd .snd ) ) )

  body-in : LeafBnd δ
          → ⟨ δ ⊨ StepBody B₁ F₁ ⟩ → ⟨ δ ⊨ StepStory.BodyB v b f ⟩
  body-in bnd h =
    ( h .fst
    , ( h .snd .fst
      , ( leaf-in bnd (h .snd .snd .fst)
        , h .snd .snd .snd ) ) )

-- The clause-level agreement.  OUT: the delivered machine step satisfies
-- the bounded story.  IN: the bounded story assembles the delivered
-- machine step.
module StepAgree {n : ℕ} (v b f : Fin n) (γ : S ^ suc n) where
  private
    K V₁ B₁ F₁ : Fin (suc n)
    K  = zero
    V₁ = suc v
    B₁ = suc b
    F₁ = suc f

  Φ : Formula S (suc (suc n))
  Φ = ∃̇ (∃̇ (∃̇ (StepBody B₁ F₁)))

  -- The outer three bound facts, stated on the delivered body.
  OuterBnd : (z : S) → Type (ℓ-suc ℓ)
  OuterBnd z =
      (c w d : S) → ⟨ (d ∷ w ∷ c ∷ z ∷ γ) ⊨ StepBody B₁ F₁ ⟩
                  → ⟨ fst c ∈ fst (lookup B₁ γ) ⟩
                  × ( ⟨ fst w ∈ fst (lookup K γ) ⟩
                    × ⟨ fst d ∈ fst (lookup K γ) ⟩ )

  -- The leaf bound facts, at the body context built from the witnesses.
  LeafFacts : (z : S) → Type (ℓ-suc ℓ)
  LeafFacts z = (c w d : S) → LeafBnd {n} (d ∷ w ∷ c ∷ z ∷ γ)

  -- The body agreement at the module level, so the LeafBnd type is
  -- elaborated once with plain parameters, not inside the decode lambdas.
  body-in-lemma : (z c w d : S) → LeafBnd {n} (d ∷ w ∷ c ∷ z ∷ γ)
                → ⟨ (d ∷ w ∷ c ∷ z ∷ γ) ⊨ StepBody B₁ F₁ ⟩
                → ⟨ (d ∷ w ∷ c ∷ z ∷ γ) ⊨ StepStory.BodyB v b f ⟩
  body-in-lemma z c w d bnd = BodyAgree.body-in {n} v b f (d ∷ w ∷ c ∷ z ∷ γ) bnd

  body-out-lemma : (z c w d : S) → LeafBnd {n} (d ∷ w ∷ c ∷ z ∷ γ)
                 → ⟨ (d ∷ w ∷ c ∷ z ∷ γ) ⊨ StepStory.BodyB v b f ⟩
                 → ⟨ (d ∷ w ∷ c ∷ z ∷ γ) ⊨ StepBody B₁ F₁ ⟩
  body-out-lemma z c w d bnd = BodyAgree.body-out {n} v b f (d ∷ w ∷ c ∷ z ∷ γ) bnd

  wit-out : (z : S) → LeafFacts z
          → ⟨ (z ∷ γ) ⊨ StepStory.StepWitB v b f ⟩ → ⟨ (z ∷ γ) ⊨ Φ ⟩
  wit-out z lf = PT.rec (snd ((z ∷ γ) ⊨ Φ))
    (λ { (c₀ , (_ , h₁)) → PT.rec (snd ((z ∷ γ) ⊨ Φ))
      (λ { (w₀ , (_ , h₂)) → PT.rec (snd ((z ∷ γ) ⊨ Φ))
        (λ { (d₀ , (_ , hb)) →
          ∣ c₀ , ∣ w₀ , ∣ d₀ , body-out-lemma z c₀ w₀ d₀ (lf c₀ w₀ d₀) hb
                  ∣₁ ∣₁ ∣₁ }) h₂ }) h₁ })

  wit-in : (z : S) → OuterBnd z → LeafFacts z
         → ⟨ (z ∷ γ) ⊨ Φ ⟩ → ⟨ (z ∷ γ) ⊨ StepStory.StepWitB v b f ⟩
  wit-in z ob lf = PT.rec (snd ((z ∷ γ) ⊨ StepStory.StepWitB v b f))
    (λ { (c₀ , h₁) → PT.rec (snd ((z ∷ γ) ⊨ StepStory.StepWitB v b f))
      (λ { (w₀ , h₂) → PT.rec (snd ((z ∷ γ) ⊨ StepStory.StepWitB v b f))
        (λ { (d₀ , hb) →
          let b = ob c₀ w₀ d₀ hb
          in ∣ c₀ , ( b .fst
                    , ∣ w₀ , ( b .snd .fst
                            , ∣ d₀ , ( b .snd .snd
                                    , body-in-lemma z c₀ w₀ d₀ (lf c₀ w₀ d₀) hb ) ∣₁ ) ∣₁ ) ∣₁ })
          h₂ }) h₁ })

  -- OUT: the delivered machine step satisfies the bounded story.
  step-out : ((z : S) → OuterBnd z) → ((z : S) → LeafFacts z)
           → ⟨ γ ⊨ StepAt V₁ B₁ F₁ ⟩ → ⟨ γ ⊨ StepStory.StepBndB v b f ⟩
  step-out ob lf h = extAt-in-both V₁ (StepStory.StepWitB v b f) γ
    (λ z z∈ → wit-in z (ob z) (lf z) (extAt-out V₁ Φ γ h z z∈))
    (λ z hw → extAt-in V₁ Φ γ h z (wit-out z (lf z) hw))

  -- IN: the bounded story assembles the delivered machine step.
  step-in : ((z : S) → OuterBnd z) → ((z : S) → LeafFacts z)
          → ⟨ γ ⊨ StepStory.StepBndB v b f ⟩ → ⟨ γ ⊨ StepAt V₁ B₁ F₁ ⟩
  step-in ob lf h = extAt-in-both V₁ Φ γ
    (λ z z∈ → wit-out z (lf z) (extAt-out V₁ (StepStory.StepWitB v b f) γ h z z∈))
    (λ z hu → extAt-in V₁ (StepStory.StepWitB v b f) γ h z
                (wit-in z (ob z) (lf z) hu))

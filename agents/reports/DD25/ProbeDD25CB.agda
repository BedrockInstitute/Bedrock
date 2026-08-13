{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.33] The probe for leg D: the story-to-machine agreement at L.
-- One clause's decode against the delivered machine's projections, at
-- variable slots.  The story side is the bounded step clause in the
-- Clause style of src/L/Condensation.lagda.md; the machine side is the
-- delivered StepAt with its projections StepAt-out / StepAt-in from
-- src/L/Coding/Sequence.lagda.md:217-229, and the step formula's own
-- extAt readings from src/L/Coding/Model.lagda.md:662-678.  Untracked
-- probe; one Agda process under GHCRTS="-A64m -I0 -M8g"; never
-- committed; thrown away per D-1.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeDD25CB {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; var; _∈̇_; _∧̇_; _⇒̇_; ∃̇_; ∀̇_; ∃̇∈ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; 𝒟ₒ )
open import L.Coding.Model {ℓ}
  using ( appAt; appAt-adequate; extAt; extAt-out; extAt-in )
open import L.Coding.Powerset {ℓ} lem
  using ( DefAt; DefAt-in; DefAt-out; DefOK )
open import L.Coding.Sequence {ℓ} lem
  using ( StepAt; StepBody; Records; StepOf; PowOK
        ; StepAt-out; StepAt-in )
open import L.Condensation {ℓ} lem
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

-- =====================================================================
-- SECTION 1: THE STORY'S STEP CLAUSE, in the Clause style.
-- The machine's step (StepAt, src/L/Coding/Sequence.lagda.md:135-145)
-- says: the value v at the argument b from the approximation f is the
-- set of exactly those z for which there are c in b, w recorded by f
-- at c, and the definable powerset d of w, with z in d.  The bounded
-- restatement bounds the three existentials: c by b, w by the bound K,
-- d by the bound K.  Arity suc n: the bound sits at slot zero, the
-- machine's slots v b f are shifted by one.  This mirrors the Clause
-- module's shape (src/L/Condensation.lagda.md:52-195): the bounded
-- matrix at variable slots, with the bound at slot zero.  The clause's
-- Delta-0 certificate is a separate row (the bounded step stack,
-- LJ-1.2's NO-GO); this probe measures the decode, which needs no
-- certificate.
-- =====================================================================
module StepStory {n : ℕ} (K : Fin (suc n)) (v b f : Fin n) where
  private
    V₁ B₁ F₁ : Fin (suc n)
    V₁ = suc v
    B₁ = suc b
    F₁ = suc f

  -- The body, at env d ∷ w ∷ c ∷ z ∷ γ (arity 5 + n).  It is
  -- definitionally the delivered StepBody at the shifted slots
  -- (StepBody B F), with every gamma-slot index shifted by one for the
  -- bound at slot zero.
  Body : Formula S (5 + n)
  Body = StepBody B₁ F₁

  -- The witness content, at env z ∷ γ (arity 2 + n): c in b, w in K,
  -- d in K, with the body.
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

  -- The bounded step clause, at env γ (arity suc n): the extension,
  -- both directions, exactly the machine's extAt shape.
  StepBnd : Formula S (suc n)
  StepBnd = StepIn ∧̇ StepOut

-- =====================================================================
-- SECTION 2: THE STORY-TO-MACHINE DECODE, at variable slots.
-- The machine side is the delivered StepAt at the same environment.
-- OUT reads a satisfied machine step into the bounded story (the
-- StepAt-out projection supplies the step's own content); IN assembles
-- the machine step from the bounded story (the StepAt-in projection
-- consumes it).  DefAt-in / DefAt-out are the delivered powerset
-- readings.  The bound construction is a HYPOTHESIS here: the bound K
-- must contain every recorded value and its definable powerset.  That
-- content is the carrier-facts row, not this row.
-- =====================================================================
module StepAgree {n : ℕ} (K : Fin (suc n)) (v b f : Fin n) (γ : S ^ suc n) where
  private
    V₁ B₁ F₁ : Fin (suc n)
    V₁ = suc v
    B₁ = suc b
    F₁ = suc f

    -- The machine's step body at the shifted slots: the same content
    -- as the story's Body, definitionally.
    Φ : Formula S (suc (suc n))
    Φ = ∃̇ (∃̇ (∃̇ (StepBody B₁ F₁)))

  -- The bound construction: the bound contains the recorded values and
  -- their definable powersets.
  BoundOK : Type (ℓ-suc ℓ)
  BoundOK =
      ((c w : S) → Records B₁ F₁ γ c w → ⟨ fst w ∈ fst (lookup K γ) ⟩)
    × ((c w : S) → Records B₁ F₁ γ c w → ⟨ 𝒟ₒ (fst w) ∈ fst (lookup K γ) ⟩)

  -- OUT, first direction: a satisfied machine step, the delivered
  -- StepAt-out content, and the bound construction give the bounded
  -- story's witness content.
  step-out₁ : ⟨ γ ⊨ StepAt V₁ B₁ F₁ ⟩ → PowOK B₁ F₁ γ → BoundOK
            → ⟨ γ ⊨ StepStory.StepIn K v b f ⟩
  step-out₁ h ok (bw , bd) z z∈v =
    PT.rec (snd ((z ∷ γ) ⊨ StepStory.StepWit K v b f)) go
      (StepAt-out {suc n} V₁ B₁ F₁ γ h ok z z∈v)
    where
    go : StepOf B₁ F₁ γ z → ⟨ (z ∷ γ) ⊨ StepStory.StepWit K v b f ⟩
    go (c , (w , (rec , hz))) =
      ∣ c , (rec .fst , ∣ w , (bw c w rec , ∣ d , (bd c w rec , body) ∣₁) ∣₁) ∣₁
      where
      d : S
      d = 𝒟ₒ (fst w) , ok c w rec

      ha : ⟨ (d ∷ w ∷ c ∷ z ∷ γ)
              ⊨ appAt (suc (suc (suc (suc (suc f)))))
                      (suc (suc zero)) (suc zero) ⟩
      ha = subst ⟨_⟩ (sym (appAt-adequate (suc (suc (suc (suc (suc f)))))
                                          (suc (suc zero)) (suc zero)
                                          (d ∷ w ∷ c ∷ z ∷ γ))) (rec .snd)

      hdef : ⟨ (d ∷ w ∷ c ∷ z ∷ γ) ⊨ DefAt zero (suc zero) ⟩
      hdef = DefAt-in w zero (suc zero) (d ∷ w ∷ c ∷ z ∷ γ) refl refl

      body : ⟨ (d ∷ w ∷ c ∷ z ∷ γ) ⊨ StepBody B₁ F₁ ⟩
      body = (rec .fst , (ha , (hdef , hz)))

  -- OUT, second direction: a satisfied machine step reads the bounded
  -- witness back into the value, through the step formula's own
  -- extAt-in reading with the bounds dropped.
  step-out₂ : ⟨ γ ⊨ StepAt V₁ B₁ F₁ ⟩ → PowOK B₁ F₁ γ → BoundOK
            → ⟨ γ ⊨ StepStory.StepOut K v b f ⟩
  step-out₂ h ok bounds z hw = h .snd z (dropB z hw)
    where
    dropB : (z : S) → ⟨ (z ∷ γ) ⊨ StepStory.StepWit K v b f ⟩ → ⟨ (z ∷ γ) ⊨ Φ ⟩
    dropB z = PT.rec (snd ((z ∷ γ) ⊨ Φ)) (λ { (c , (c∈b , hw')) →
      PT.rec (snd ((z ∷ γ) ⊨ Φ)) (λ { (w , (w∈K , hd')) →
        PT.rec (snd ((z ∷ γ) ⊨ Φ)) (λ { (d , (d∈K , body)) →
          ∣ c , ∣ w , ∣ d , body ∣₁ ∣₁ ∣₁ }) hd' }) hw' })

  -- OUT: the machine step satisfies the bounded story.
  step-out : ⟨ γ ⊨ StepAt V₁ B₁ F₁ ⟩ → PowOK B₁ F₁ γ → BoundOK
           → ⟨ γ ⊨ StepStory.StepBnd K v b f ⟩
  step-out h ok bounds = (step-out₁ h ok bounds , step-out₂ h ok bounds)

  -- IN, first direction: the bounded witness is the machine step's own
  -- content, given to the delivered StepAt-in projection.
  step-in₁ : ⟨ γ ⊨ StepStory.StepBnd K v b f ⟩ → PowOK B₁ F₁ γ → BoundOK
           → (z : S) → ⟨ fst z ∈ fst (lookup V₁ γ) ⟩ → ∥ StepOf B₁ F₁ γ z ∥₁
  step-in₁ h ok (bw , bd) z z∈v =
    PT.rec squash₁ (λ { (c , (c∈b , hw')) →
      PT.rec squash₁ (λ { (w , (w∈K , hd')) →
        PT.rec squash₁ (λ { (d , (d∈K , body)) →
          ∣ c , w , ((c∈b , ha c w d z body) , hz c w d z body) ∣₁ }) hd' }) hw' })
      (h .fst z z∈v)
    where
    ha : (c w d z : S) → ⟨ (d ∷ w ∷ c ∷ z ∷ γ) ⊨ StepBody B₁ F₁ ⟩
       → ⟨ pr (fst c) (fst w) ∈ fst (lookup F₁ γ) ⟩
    ha c w d z body =
      subst ⟨_⟩ (appAt-adequate (suc (suc (suc (suc (suc f)))))
                                (suc (suc zero)) (suc zero)
                                (d ∷ w ∷ c ∷ z ∷ γ))
        (body .snd .fst)

    hz : (c w d z₀ : S) → ⟨ (d ∷ w ∷ c ∷ z₀ ∷ γ) ⊨ StepBody B₁ F₁ ⟩
       → ⟨ fst z₀ ∈ 𝒟ₒ (fst w) ⟩
    hz c w d z₀ body =
      subst (λ X → ⟨ fst z₀ ∈ X ⟩)
        (DefAt-out w zero (suc zero) (d ∷ w ∷ c ∷ z ∷ γ)
          okD refl (body .snd .snd .fst))
        (body .snd .snd .snd)
      where
      c∈b : ⟨ fst c ∈ fst (lookup B₁ γ) ⟩
      c∈b = body .fst
      okD : DefOK w
      okD x x∈ =
        isL-trans {x = 𝒟ₒ (fst w)} {y = x} x∈ (ok c w (c∈b , ha c w d z₀ body))

  -- IN, second direction: the machine step's own content assembles the
  -- bounded witness, and the bounded story reads it back into the
  -- value.
  step-in₂ : ⟨ γ ⊨ StepStory.StepBnd K v b f ⟩ → PowOK B₁ F₁ γ → BoundOK
           → (z : S) → StepOf B₁ F₁ γ z → ⟨ fst z ∈ fst (lookup V₁ γ) ⟩
  step-in₂ h ok (bw , bd) z (c , (w , (rec , hz))) = h .snd z writeWit
    where
    d : S
    d = 𝒟ₒ (fst w) , ok c w rec

    ha : ⟨ (d ∷ w ∷ c ∷ z ∷ γ)
            ⊨ appAt (suc (suc (suc (suc (suc f)))))
                    (suc (suc zero)) (suc zero) ⟩
    ha = subst ⟨_⟩ (sym (appAt-adequate (suc (suc (suc (suc (suc f)))))
                                        (suc (suc zero)) (suc zero)
                                        (d ∷ w ∷ c ∷ z ∷ γ))) (rec .snd)

    hdef : ⟨ (d ∷ w ∷ c ∷ z ∷ γ) ⊨ DefAt zero (suc zero) ⟩
    hdef = DefAt-in w zero (suc zero) (d ∷ w ∷ c ∷ z ∷ γ) refl refl

    body : ⟨ (d ∷ w ∷ c ∷ z ∷ γ) ⊨ StepBody B₁ F₁ ⟩
    body = (rec .fst , (ha , (hdef , hz)))

    writeWit : ⟨ (z ∷ γ) ⊨ StepStory.StepWit K v b f ⟩
    writeWit =
      ∣ c , (rec .fst , ∣ w , (bw c w rec , ∣ d , (bd c w rec , body) ∣₁) ∣₁) ∣₁

  -- IN: the bounded story assembles the machine step, through the
  -- delivered StepAt-in projection.
  step-in : ⟨ γ ⊨ StepStory.StepBnd K v b f ⟩ → PowOK B₁ F₁ γ → BoundOK
          → ⟨ γ ⊨ StepAt V₁ B₁ F₁ ⟩
  step-in h ok bounds =
    StepAt-in {suc n} V₁ B₁ F₁ γ ok (step-in₁ h ok bounds) (step-in₂ h ok bounds)

{-# OPTIONS --cubical --safe --guardedness #-}

------------------------------------------------------------------------
-- [L3.31-IF-Ip] D-1 probe: ONE level-story reading, generic in the
-- carrier.  Untracked; no master touched; Everything untouched.
--
-- Subject: the DefAt-class clause at L/Coding/Sequence.lagda.md:361-379,
-- i.e. the `GraphOf` / `LsetGraph-in` / `LsetGraph-out` reading of
-- `LsetGraph`: the satisfaction of the story's one existential over its
-- two conjuncts IS the truncated sigma of the two conjunct satisfactions.
--
-- Claim under test (ifrecon §3, §8.5 first bullet; D-16): the reading is
-- generic in the restriction class.  Written once, the carrier/structure
-- a module parameter (P-h), it instantiates at 𝒮ʟ AND at a transitive
-- set carrier, both green, at a small line premium over the delivered
-- monomorphic twin.
--
-- Hypothesis ledger (the brief's "record every hypothesis the generic
-- reading consumes"):
--   * the READING (`GenericRead`) consumes NO hypotheses: `In` is the
--     truncation intro, `Out` is the definitional identity between the
--     satisfaction of the existential and the truncated sigma of the
--     conjunct satisfactions (hPropAlgebra ⋁ / ⊓ clauses);
--   * the 𝒮ʟ instantiation consumes only the delivered story (`𝒮ʟ`,
--     `ApproxAt`, `StepAt`, `LsetGraphAt`; `lem` to import the chapter);
--   * the set-carrier instantiation consumes `M` + `isTransV M` (the
--     carrier's defining property, via `Single`) and, ONLY to move the
--     delivered 𝒮ʟ-formulas to M, the two `BoundedFo` certificates (the
--     W1' BoundedFo row, priced separately).  The reading itself never
--     sees the certificates.
------------------------------------------------------------------------

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeGenericRead {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( ZFStructure; module hPropStructure )
open import FOL.Syntax using ( Formula; var; _∈̇_; _∧̇_; ¬̇_; ∃̇_ )
import FOL.Semantics
import FOL.Absoluteness
open import FOL.Manipulation.Bounding using ( BoundedFo; module Relabel )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; isTransV )
open import L.Coding.Sequence {ℓ} lem
  using ( StepAt; ApproxAt; LsetGraphAt )

open import Cubical.Data.Sigma using ( _×_; _,_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

open hPropStructure 𝒮ᵥ renaming ( S to SV )

module SemV = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ
open SemV using ( _^_ )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans

Sʟ : Type (ℓ-suc ℓ)
Sʟ = AbsL.SM

------------------------------------------------------------------------
-- THE READING, ONCE.  P-h: the carrier/structure is a module parameter;
-- the reading never mentions a concrete carrier body or a concrete
-- formula body.
------------------------------------------------------------------------

module GenericRead {𝓁 : Level} (𝒮 : ZFStructure (hPropAlgebra 𝓁))
                   {n : ℕ} (A B : Formula (ZFStructure.S 𝒮) (suc n))
                   (γ : ZFStructure.S 𝒮 ^ n) where

  open ZFStructure 𝒮
  open TruthAlgebra (hPropAlgebra 𝓁)
  module Sem = FOL.Semantics (hPropAlgebra 𝓁) 𝒮

  _⊨_ : ∀ {m} → S ^ m → Formula S m → Ω
  _⊨_ = Sem.At._⊨_ S (λ x → x)

  Payload : Type 𝓁
  Payload = Σ[ f ∈ S ] ( ⟨ (f ∷ γ) ⊨ A ⟩ × ⟨ (f ∷ γ) ⊨ B ⟩ )

  In : (f : S)
     → ⟨ (f ∷ γ) ⊨ A ⟩ → ⟨ (f ∷ γ) ⊨ B ⟩ → ⟨ γ ⊨ (∃̇ (A ∧̇ B)) ⟩
  In f ha hb = ∣ f , (ha , hb) ∣₁

  Out : ⟨ γ ⊨ (∃̇ (A ∧̇ B)) ⟩ → ∥ Payload ∥₁
  Out h = h

------------------------------------------------------------------------
-- INSTANTIATION 1: at 𝒮ʟ, over the delivered level story.  The
-- recovered wrappers restate the delivered twin's shapes verbatim, so
-- the generic clause IS the delivered reading up to definitional
-- equality (`LsetGraphAt y x` unfolds to `∃̇ (A ∧̇ B)`).
------------------------------------------------------------------------

module AtLStory (n : ℕ) (y x : Fin n) (γ : Sʟ ^ n) where

  module R = GenericRead {𝓁 = ℓ-suc ℓ} 𝒮ʟ {n = n}
                  (ApproxAt zero (suc x)) (StepAt (suc y) (suc x) zero) γ

  GraphOf' : Type (ℓ-suc ℓ)
  GraphOf' = R.Payload

  graph-in : (f : Sʟ)
           → ⟨ (f ∷ γ) R.⊨ ApproxAt zero (suc x) ⟩
           → ⟨ (f ∷ γ) R.⊨ StepAt (suc y) (suc x) zero ⟩
           → ⟨ γ R.⊨ LsetGraphAt y x ⟩
  graph-in f ha hs = R.In f ha hs

  graph-out : ⟨ γ R.⊨ LsetGraphAt y x ⟩ → ∥ GraphOf' ∥₁
  graph-out h = R.Out h

------------------------------------------------------------------------
-- INSTANTIATION 2: at a transitive SET carrier.  `Single` builds the
-- restricted structure in one line; the delivered formulas are moved by
-- the certified `Relabel` transport, which is the only consumer of the
-- two `BoundedFo` certificates.  The reading itself never sees them.
------------------------------------------------------------------------

module AtCarrier (M : SV) (Mtr : isTransV M) where

  module AbsM = FOL.Absoluteness.Single 𝒮ᵥ (λ x → x ∈ˢ M) Mtr

  InM : Sʟ → Type (ℓ-suc ℓ)
  InM c = ⟨ fst c ∈ˢ M ⟩

  -- The reading at the set carrier with CONSUMER-SUPPLIED formulas:
  -- zero certificates, zero transport (the cured form, R-37 / P-i [A]).
  module ReadingAtM {n : ℕ} (A' B' : Formula AbsM.SM (suc n))
                    (γᴹ : AbsM.SM ^ n) where
    module R0 = GenericRead {𝓁 = ℓ-suc ℓ} AbsM.𝒮M {n = n} A' B' γᴹ

  module Down = Relabel {K = Sʟ} {K' = AbsM.SM} {W = SV}
                  fst fst InM (λ c p → fst c , p) (λ c p → refl)

  module LStoryAtM (n : ℕ) (y x : Fin n) (γᴹ : AbsM.SM ^ n)
                   (hA : BoundedFo InM (ApproxAt zero (suc x)))
                   (hB : BoundedFo InM (StepAt (suc y) (suc x) zero))
                   where

    liftedA : Formula AbsM.SM (suc n)
    liftedA = Down.liftFo (ApproxAt zero (suc x)) hA

    liftedB : Formula AbsM.SM (suc n)
    liftedB = Down.liftFo (StepAt (suc y) (suc x) zero) hB

    module R = GenericRead {𝓁 = ℓ-suc ℓ} AbsM.𝒮M {n = n} liftedA liftedB γᴹ

    PayloadM : Type (ℓ-suc ℓ)
    PayloadM = R.Payload

    level-in : (f : AbsM.SM)
             → ⟨ (f ∷ γᴹ) AbsM.⊨ᵐ liftedA ⟩
             → ⟨ (f ∷ γᴹ) AbsM.⊨ᵐ liftedB ⟩
             → ⟨ γᴹ AbsM.⊨ᵐ (∃̇ (liftedA ∧̇ liftedB)) ⟩
    level-in f ha hb = R.In f ha hb

    level-out : ⟨ γᴹ AbsM.⊨ᵐ (∃̇ (liftedA ∧̇ liftedB)) ⟩ → ∥ PayloadM ∥₁
    level-out h = R.Out h

    -- C-6 positive control: same-clause swap checks at the set carrier.
    module Swap = GenericRead {𝓁 = ℓ-suc ℓ} AbsM.𝒮M {n = n} liftedB liftedA γᴹ

------------------------------------------------------------------------
-- C-6 perturbation controls on the claim "the reading consumes no
-- hypothesis of the story's own content":
--   * positive: at 𝒮ʟ the clause checks for a NON-story garbage pair
--     of formulas, so nothing about ApproxAt/StepAt is used by it;
--   * negative (run during development, then removed): claiming `Out`
--     at the swapped conjunct order, and claiming `In` while dropping
--     the second conjunct proof, are both rejected by the typechecker.
------------------------------------------------------------------------

module PerturbL (n : ℕ) (γ : Sʟ ^ n) where

  junk1 : Formula Sʟ (suc n)
  junk1 = var zero ∈̇ var zero

  junk2 : Formula Sʟ (suc n)
  junk2 = ¬̇ (var zero ∈̇ var zero)

  module Rj = GenericRead {𝓁 = ℓ-suc ℓ} 𝒮ʟ {n = n} junk1 junk2 γ

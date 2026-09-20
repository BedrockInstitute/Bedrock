{-# OPTIONS --cubical --safe --guardedness #-}

-- K5 Track H, seam 3: the reverse translation and its entry law are K3's.
--
-- WHAT IT CHECKS. K5/RoundTrip.agda takes trᴾ and its entry law as two module
-- parameters, typed by hand from TranslateReverse.agda:548-549 and :656-659.
-- Ledger clause L10 says a cross-track parameter is typed verbatim from the
-- producing export so that a DRIFT FAILS IN A PROBE instead of passing
-- silently. This file is that probe for the REVERSE half: it applies the real
-- module Over over the real telescope and states the entry law Track H assumes
-- as a path proved by TranslateReverse's own theorem. It also checks trᴾ-name,
-- which module Named of the deliverable uses to package surjectivity.
--
-- The FORWARD half is already probed and does not need repeating here: Track E
-- applies TranslateForward's Target over the real telescope and checks the
-- same entry law as a path (K5/AgreementAtTranslation.agda:145-152), in the
-- instantiated spelling iCode := λ q → fst (i q) that K5/RoundTripAtUof.agda
-- substitutes. Track H's parameter is the abstract spelling with iCode a
-- variable, so the two compose: Track E's probe checks the law at the
-- instantiation and the deliverable states it at the variable.
--
-- One heavy module application, rule 10: TranslateReverse's Over. Every
-- argument to it is a variable of this module, so preamble rule 2's tightest
-- seal holds and rule 2b cannot be reached.
--
-- WHAT THIS PROBE IS NOT. It does not build an inhabitant of anything. image
-- and image-spec are K3's tier-4 MemberImage and they are VARIABLES here, so
-- this file makes no claim that trᴾ exists at any ground, and in particular
-- none at L; obstruction O3 stands exactly where K3 left it.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
open import Cubical.Induction.WellFounded using ( WellFounded )
import K4.Algebra
import TranslateReverse

module K5.RoundTripAtReverse {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.ZFModel 𝒮 using ( _⊆ˢ_ )
open import CodedVocabulary 𝒮 using ( isKPairΔ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

open K4.Algebra 𝒮 using ( Pt )

-- The nine Names parameters of TranslateReverse.agda:357-367, the four Ground
-- parameters of :389-396, and the twelve Over parameters of :452-467.

module Seam
  (entry           : S → S → S)
  (entry-inj       : {x b y c : S} → entry x b ≡ entry y c
                   → (x ≡ y) × (b ≡ c))
  (entry-isKPair   : (x b : S) → ⟨ isKPairΔ (entry x b) x b ⟩)
  (Child           : S → S → Type ℓ)
  (child-entry     : (x b n : S) → ⟨ entry x b ∈ˢ n ⟩ → Child x n)
  (child-elim      : (x n : S) (Q : Ω) → Child x n
                   → ((b : S) → ⟨ entry x b ∈ˢ n ⟩ → ⟨ Q ⟩) → ⟨ Q ⟩)
  (child-wf        : WellFounded Child)
  (≈ˢ-paths        : (x y : S) → (x ≈ˢ y) ≡ ((x ≡ y) , isSetS x y))
  (ext-path        : {a b : S} → ((x : S) → (x ∈ˢ a) ≡ (x ∈ˢ b)) → a ≡ b)
  (image           : (a : S) (f : (Σ[ x ∈ S ] ⟨ x ∈ˢ a ⟩) → S) → S)
  (image-spec      : (a : S) (f : (Σ[ x ∈ S ] ⟨ x ∈ˢ a ⟩) → S) (z : S)
                   → (z ∈ˢ image a f)
                   ≡ ⋁ S (λ x → ⋁ ⟨ x ∈ˢ a ⟩ (λ h → z ≈ˢ f (x , h))))
  (unionOf         : S → S)
  (unionOf-spec    : (t z : S) → (z ∈ˢ unionOf t)
                   ≡ ⋁ S (λ u → (u ∈ˢ t) ⊓ (z ∈ˢ u)))
  (carrier B       : S)
  (below           : (Σ[ b ∈ S ] ⟨ b ∈ˢ B ⟩) → S)
  (below-sub       : (b : Σ[ b ∈ S ] ⟨ b ∈ˢ B ⟩) → ⟨ below b ⊆ˢ carrier ⟩)
  (supportᴮ        : S → S)
  (weightsAt       : S → S → S)
  (support-outᴮ    : (n x : S) → ⟨ x ∈ˢ supportᴮ n ⟩ → Child x n)
  (support-entryᴮ  : (n x b : S) → ⟨ b ∈ˢ B ⟩ → ⟨ entry x b ∈ˢ n ⟩
                   → ⟨ x ∈ˢ supportᴮ n ⟩)
  (support-weightᴮ : (n x : S) → ⟨ x ∈ˢ supportᴮ n ⟩
                   → ⟨ ⋁ S (λ b → b ∈ˢ weightsAt n x) ⟩)
  (weightsAt-sub   : (n x b : S) → ⟨ b ∈ˢ weightsAt n x ⟩ → ⟨ b ∈ˢ B ⟩)
  (weightsAt-in    : (n x b : S) → ⟨ b ∈ˢ B ⟩ → ⟨ entry x b ∈ˢ n ⟩
                   → ⟨ b ∈ˢ weightsAt n x ⟩)
  (weightsAt-out   : (n x b : S) → ⟨ b ∈ˢ weightsAt n x ⟩
                   → ⟨ entry x b ∈ˢ n ⟩)
  where

  module TR = TranslateReverse.Names.Ground.Over 𝒮
                entry entry-inj entry-isKPair Child child-entry child-elim
                child-wf ≈ˢ-paths ext-path
                image image-spec unionOf unionOf-spec
                carrier B below below-sub supportᴮ weightsAt
                support-outᴮ support-entryᴮ support-weightᴮ
                weightsAt-sub weightsAt-in weightsAt-out

  -- THE CHECK, in the sharp form: not that the arity matches but that the
  -- PROPOSITION matches, at every pair of codes. Track H's parameter type is
  -- on the left of the colon and TranslateReverse's theorem is on the right.
  -- The type is Pt B's Σ written as K3 writes it; Track H writes below at
  -- Pt B, which is the same Σ (K4/Algebra.agda:58-59) and not a second one.

  entry-law-agrees : (n e : S) → (e ∈ˢ TR.trᴾ n)
                   ≡ ⋁ S (λ x → ⋁ S (λ b → ⋁ ⟨ b ∈ˢ B ⟩ (λ hb → ⋁ S (λ p →
                       (entry x b ∈ˢ n) ⊓ ((p ∈ˢ below (b , hb))
                          ⊓ (e ≈ˢ entry (TR.trᴾ x) p))))))
  entry-law-agrees = TR.trᴾ-entries

  -- And that `below` may be read at Pt B without a coercion, which is what
  -- lets the deliverable state its telescope in K4.Algebra's vocabulary while
  -- K3 states its own in the raw Σ.

  below-at-Pt : Pt B → S
  below-at-Pt = below

--------------------------------------------------------------------------------
-- The name law, for the surjectivity packaging
--------------------------------------------------------------------------------

  -- Module Named of K5/RoundTrip.agda takes trᴾ-name and spends ⟨ IsNameᴮ n ⟩
  -- there and nowhere else. The four parameters below are
  -- TranslateReverse.agda:742-751 and the check is the same shape.

  module Valid
    (IsNameᴮ        : S → Ω)
    (child-is-nameᴮ : (n : S) → ⟨ IsNameᴮ n ⟩ → (x : S) → Child x n
                    → ⟨ IsNameᴮ x ⟩)
    (IsNameᴾ        : S → Ω)
    (entries-nameᴾ  : (n : S)
                    → ((e : S) → ⟨ e ∈ˢ n ⟩
                       → ∥ Σ[ x ∈ S ] Σ[ p ∈ S ]
                           ((e ≡ entry x p)
                            × (⟨ p ∈ˢ carrier ⟩ × ⟨ IsNameᴾ x ⟩)) ∥₁)
                    → ⟨ IsNameᴾ n ⟩)
    where

    module TV = TR.Valid IsNameᴮ child-is-nameᴮ IsNameᴾ entries-nameᴾ

    name-law-agrees : (n : S) → ⟨ IsNameᴮ n ⟩ → ⟨ IsNameᴾ (TR.trᴾ n) ⟩
    name-law-agrees = TV.trᴾ-name

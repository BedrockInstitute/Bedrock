{-# OPTIONS --cubical --safe --guardedness #-}

-- K5 Track E, seam probe 1. Evidence, not a deliverable.
--
-- WHAT IT CHECKS. K5/Agreement.agda takes the forward translation and its
-- entry law as two module parameters, typed by hand from
-- TranslateForward.agda:387 and :436-442 with the one substitution the
-- instantiation makes, iCode := λ q → fst (i q). Ledger clause L10 says a
-- cross-track parameter is typed verbatim from the producing export so that a
-- DRIFT FAILS IN A PROBE instead of passing silently. This file is that
-- probe: it applies the real Target layer over the real telescope, and hands
-- its trᴮ and trᴮ-entries to Track E's Translation module. If either type has
-- drifted by a single argument the application below does not typecheck.
--
-- It also checks the thing the architecture asserts without compiling it: at
-- a ForcingBase, the Target layer's two separate embedding parameters iCode
-- and i∈B are the two projections of the single field i, and Σ's eta makes
-- (fst (i q) , snd (i q)) the field itself. That is why Track E's entry law
-- may be written with fst (i (p , hp)) where the producing file writes
-- iCode (p , hp).
--
-- One heavy module application, rule 10: TranslateForward's Target. Every
-- argument to it is a variable of this module.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
open import Cubical.Induction.WellFounded using ( WellFounded )
import K4.Algebra
import K5.Frame
import K5.Agreement
import TranslateForward

module K5.AgreementAtTranslation {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

open K4.Algebra 𝒮 using ( Pt; Lattice; Complement )

module Probe (carrier order : S) where

  open K5.Frame.Poset 𝒮 carrier order using ( Cond; ForcingBase )

  -- The nine Kernel parameters of TranslateForward.agda:144-154. Seven are
  -- shared with K3's value module and with Track E's Kernel telescope, so
  -- passing one variable to both is itself a drift check between the two
  -- consumers of the name kernel.

  module Seam
    (entry          : S → S → S)
    (entry-inj      : {x b y c : S} → entry x b ≡ entry y c
                    → (x ≡ y) × (b ≡ c))
    (Child          : S → S → Type ℓ)
    (isPropChild    : (x n : S) → isProp (Child x n))
    (child-entry    : (x b n : S) → ⟨ entry x b ∈ˢ n ⟩ → Child x n)
    (child-weight   : (x n : S) → Child x n
                    → ∥ Σ[ b ∈ S ] ⟨ entry x b ∈ˢ n ⟩ ∥₁)
    (child-wf       : WellFounded Child)
    (≈ˢ-paths       : (x y : S) → (x ≈ˢ y) ≡ ((x ≡ y) , isSetS x y))
    (ext-path       : {a b : S} → ((x : S) → (x ∈ˢ a) ≡ (x ∈ˢ b)) → a ≡ b)
    -- the two set existence data, TranslateForward.agda:185-193
    (image          : (a : S) (f : (Σ[ x ∈ S ] ⟨ x ∈ˢ a ⟩) → S) → S)
    (image-spec     : (a : S) (f : (Σ[ x ∈ S ] ⟨ x ∈ˢ a ⟩) → S) (z : S)
                    → (z ∈ˢ image a f)
                    ≡ ⋁ S (λ x → ⋁ ⟨ x ∈ˢ a ⟩ (λ h → z ≈ˢ f (x , h))))
    (unionOf        : S → S)
    (unionOf-spec   : (t z : S) → (z ∈ˢ unionOf t)
                    ≡ ⋁ S (λ u → (u ∈ˢ t) ⊓ (z ∈ˢ u)))
    -- the Source layer, TranslateForward.agda:261-275
    (IsNameᴾ        : S → Ω)
    (child-is-nameᴾ : (n : S) → ⟨ IsNameᴾ n ⟩ → (x : S) → Child x n
                    → ⟨ IsNameᴾ x ⟩)
    (support        : S → S)
    (supp-in        : (n x p : S) → ⟨ p ∈ˢ carrier ⟩ → ⟨ entry x p ∈ˢ n ⟩
                    → ⟨ x ∈ˢ support n ⟩)
    (supp-out       : (n x : S) → ⟨ x ∈ˢ support n ⟩
                    → ∥ Σ[ p ∈ S ] (⟨ p ∈ˢ carrier ⟩ × ⟨ entry x p ∈ˢ n ⟩) ∥₁)
    (weightsAt      : S → S → S)
    (weights-sub    : (n x p : S) → ⟨ p ∈ˢ weightsAt n x ⟩ → ⟨ p ∈ˢ carrier ⟩)
    (weights-in     : (n x p : S) → ⟨ p ∈ˢ carrier ⟩ → ⟨ entry x p ∈ˢ n ⟩
                    → ⟨ p ∈ˢ weightsAt n x ⟩)
    (weights-out    : (n x p : S) → ⟨ p ∈ˢ weightsAt n x ⟩
                    → ⟨ entry x p ∈ˢ n ⟩)
    -- the Target layer, TranslateForward.agda:324-345, minus the embedding
    (B              : S)
    (IsNameᴮ        : S → Ω)
    (name-introᴮ    : (n : S)
                    → ((e : S) → ⟨ e ∈ˢ n ⟩
                       → ∥ Σ[ y ∈ S ] Σ[ b ∈ S ]
                             (e ≡ entry y b) × ⟨ b ∈ˢ B ⟩ ∥₁)
                    → ((y : S) → Child y n → ⟨ IsNameᴮ y ⟩)
                    → ⟨ IsNameᴮ n ⟩)
    (supportᴮ       : S → S)
    (suppᴮ-in       : (n y b : S) → ⟨ b ∈ˢ B ⟩ → ⟨ entry y b ∈ˢ n ⟩
                    → ⟨ y ∈ˢ supportᴮ n ⟩)
    (suppᴮ-out      : (n y : S) → ⟨ y ∈ˢ supportᴮ n ⟩
                    → ∥ Σ[ b ∈ S ] (⟨ b ∈ˢ B ⟩ × ⟨ entry y b ∈ˢ n ⟩) ∥₁)
    (closedᴮ        : S → Ω)
    (closedᴮ-intro  : (D : S)
                    → ((m : S) → ⟨ m ∈ˢ D ⟩ → (e : S) → ⟨ e ∈ˢ m ⟩
                       → ∥ Σ[ y ∈ S ] Σ[ b ∈ S ]
                             (⟨ y ∈ˢ D ⟩ × ⟨ b ∈ˢ B ⟩ × (e ≡ entry y b)) ∥₁)
                    → ⟨ closedᴮ D ⟩)
    -- the frame, whose field i replaces the Target layer's iCode and i∈B
    (L : Lattice B) (Cm : Complement B L)
    (fb : ForcingBase B L Cm)
    -- and the empty name, which K3's value module takes and this one does not
    (∅ᴺ : S)
    (∅ᴺ-spec : (z : S) → (z ∈ˢ ∅ᴺ) ≡ ⊥)
    where

    open ForcingBase fb using ( i )

    -- THE ONE HEAVY APPLICATION. iCode and i∈B are supplied as the two
    -- projections of i; this is the substitution K5/Agreement.agda documents
    -- beside its Translation telescope.

    module TF = TranslateForward.Kernel.Weighted.Source.Target 𝒮
                  entry entry-inj Child isPropChild child-entry child-weight
                  child-wf ≈ˢ-paths ext-path
                  image image-spec unionOf unionOf-spec
                  carrier IsNameᴾ child-is-nameᴾ support supp-in supp-out
                  weightsAt weights-sub weights-in weights-out
                  B IsNameᴮ name-introᴮ supportᴮ suppᴮ-in suppᴮ-out
                  closedᴮ closedᴮ-intro
                  (λ q → fst (i q)) (λ q → snd (i q))

    -- THE CHECK. Track E's Translation telescope, fed the real translation
    -- and the real entry law. Nothing is proved here; the application is the
    -- evidence, and it fails if either type has drifted.

    module Fed = K5.Agreement.Poset.Kernel.Frame.Translation 𝒮 carrier order
                   entry entry-inj Child isPropChild child-entry child-wf
                   ∅ᴺ ∅ᴺ-spec ≈ˢ-paths
                   B L Cm fb
                   TF.trᴮ TF.trᴮ-entries

    -- And a second, sharper form of the same check, written as a path so that
    -- a drift in the STATEMENT and not merely in the arity is caught too: the
    -- entry law Track E assumes and the entry law TranslateForward proves are
    -- the same proposition at every pair of codes.

    entry-law-agrees : (n e : S)
      → ((e ∈ˢ TF.trᴮ n)
         ≡ ⋁ S (λ x → ⋁ S (λ p → ⋁ ⟨ p ∈ˢ carrier ⟩ (λ hp →
             (entry x p ∈ˢ n)
             ⊓ (e ≈ˢ entry (TF.trᴮ x) (fst (i (p , hp))))))))
    entry-law-agrees = TF.trᴮ-entries

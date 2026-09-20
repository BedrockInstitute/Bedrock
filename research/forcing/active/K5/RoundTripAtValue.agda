{-# OPTIONS --cubical --safe --guardedness #-}

-- K5 Track H, seam 1: the value surface of K5/RoundTrip.agda is K3's value
-- relation and not a fiction.
--
-- K5/RoundTrip.agda states its theorem over a value relation given by five
-- flat parameters: _≈[U]_, ‖Active‖, ≈-intro and the two readings of activity.
-- That is preamble rule 2's tightest seal and it keeps the deliverable at zero
-- heavy module applications, but it is worth nothing unless the five are
-- really K3's. This file applies Valuation.Names once, instantiates K3's
-- module Poset at the ALGEBRA exactly as Track E does (K5/Agreement.agda
-- :211-215), fills the five, and re-exports the theorem. It is Track H's one
-- budgeted heavy module application (architecture section 3.2, row H).
--
-- THE TWO SIDES ARE THE SAME RELATION, and this is the point of instantiating
-- it here rather than declaring one. VU below is character for character
-- Track E's VU, so the _≈[U]_ this file hands to the round trip and the
-- _≈[U]_ Track E's ≈-agree speaks are one definition applied to one argument
-- list, not two definitions that happen to agree. Ledger clause L12: no
-- second value relation is declared anywhere in K5, and grep for "PairRec",
-- "≈Rec" and "_≈[" in this file returns no declaration.
--
-- WHAT IS FILLED AND HOW.
--   ≈-intro     is Valuation.agda:337-343 verbatim, taken and not proved.
--   active-in   is one ∣_∣₁: Active is a Σ of four components
--               (Valuation.agda:245-248) and ‖Active‖ its truncation (:250).
--   active-out  is one PT.rec into an Ω. Trap T-E3 is honoured here and this
--               is where: Active is DATA and not a proposition, so its
--               elimination must land in a proposition, and the eliminator
--               offered takes its target Q as an Ω. There is no variant
--               returning the weight, which would be host Choice
--               (ledger clause L1).

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import K4.Algebra
import Valuation
import K5.RoundTrip

module K5.RoundTripAtValue {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import Cubical.Induction.WellFounded using ( WellFounded )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

open K4.Algebra 𝒮 using ( Pt; _≤ᴮ_; ≤ᴮ-refl; ⊆ˢ-trans; Lattice )

--------------------------------------------------------------------------------
-- The kernel, and the one application
--------------------------------------------------------------------------------

module Seam
  (entry       : S → S → S)
  (entry-inj   : {x b y c : S} → entry x b ≡ entry y c → (x ≡ y) × (b ≡ c))
  (Child       : S → S → Type ℓ)
  (isPropChild : (x n : S) → isProp (Child x n))
  (child-entry : (x b n : S) → ⟨ entry x b ∈ˢ n ⟩ → Child x n)
  (child-wf    : WellFounded Child)
  (∅ᴺ          : S)
  (∅ᴺ-spec     : (z : S) → (z ∈ˢ ∅ᴺ) ≡ ⊥)
  (paths       : (x y : S) → (x ≈ˢ y) ≡ ((x ≡ y) , isSetS x y))
  where

  module VN = Valuation.Names 𝒮 entry Child isPropChild child-entry
                                child-wf ∅ᴺ ∅ᴺ-spec

  -- K3's module Poset at the ALGEBRA. The five arguments are Track E's
  -- (K5/Agreement.agda:211-215) character for character, which is what makes
  -- the two files speak one relation. The inhabitedness the record demands is
  -- the lattice's top, a FIELD (K4/Algebra.agda:102), so it costs nothing and
  -- in particular costs no density of the image.

  module Algebra (B : S) (L : Lattice B) where

    open Lattice L using ( ⊤ᴮ )

    module VU = VN.Poset B
      (λ u v → u ≤ᴮ v)
      ≤ᴮ-refl
      (λ {u} {v} {w} h k → ⊆ˢ-trans h k)
      ∣ ⊤ᴮ ∣₁

--------------------------------------------------------------------------------
-- Track H's translation layer, with the same parameters
--------------------------------------------------------------------------------

    module Translation
      (carrier : S)
      (iCode : (Σ[ p ∈ S ] ⟨ p ∈ˢ carrier ⟩) → S)
      (i∈B   : (q : Σ[ p ∈ S ] ⟨ p ∈ˢ carrier ⟩) → ⟨ iCode q ∈ˢ B ⟩)
      (below : Pt B → S)
      (trᴮ : S → S)
      (trᴮ-entries : (n e : S) → (e ∈ˢ trᴮ n)
                   ≡ ⋁ S (λ x → ⋁ S (λ p → ⋁ ⟨ p ∈ˢ carrier ⟩ (λ hp →
                       (entry x p ∈ˢ n)
                       ⊓ (e ≈ˢ entry (trᴮ x) (iCode (p , hp)))))))
      (trᴾ : S → S)
      (trᴾ-entries : (n e : S) → (e ∈ˢ trᴾ n)
                   ≡ ⋁ S (λ x → ⋁ S (λ b → ⋁ ⟨ b ∈ˢ B ⟩ (λ hb → ⋁ S (λ p →
                       (entry x b ∈ˢ n) ⊓ ((p ∈ˢ below (b , hb))
                          ⊓ (e ≈ˢ entry (trᴾ x) p)))))))
      where

      module RT = K5.RoundTrip.Kernel.Translation 𝒮
                    entry entry-inj Child child-entry child-wf paths
                    carrier B iCode i∈B below trᴮ trᴮ-entries trᴾ trᴾ-entries

--------------------------------------------------------------------------------
-- The five value parameters, filled
--------------------------------------------------------------------------------

      module At (U : Pt B → Ω) where

        module Uv = VU.Value U

        -- Each alias below has Track H's parameter type on the left and K3's
        -- export on the right. A drift in either spelling fails here rather
        -- than passing silently; this is ledger clause L10's whole purpose and
        -- it is Track B's K5/ClausesAtFrame.agda pattern.

        seam-≈ : S → S → Ω
        seam-≈ = Uv._≈[G]_

        seam-active : S → S → Ω
        seam-active = Uv.‖Active‖

        seam-≈-intro : {m n : S}
                     → ((x : S) → ⟨ seam-active x m ⟩
                        → ⟨ ⋁ S (λ y → seam-active y n ⊓ seam-≈ x y) ⟩)
                     → ((y : S) → ⟨ seam-active y n ⟩
                        → ⟨ ⋁ S (λ x → seam-active x m ⊓ seam-≈ x y) ⟩)
                     → ⟨ seam-≈ m n ⟩
        seam-≈-intro = Uv.≈-intro

        -- An entry whose weight lies in U is active. Valuation.agda:245-251.

        seam-active-in : (x n b : S) (hb : ⟨ b ∈ˢ B ⟩)
                       → ⟨ entry x b ∈ˢ n ⟩ → ⟨ U (b , hb) ⟩
                       → ⟨ seam-active x n ⟩
        seam-active-in x n b hb he hu = ∣ b , hb , he , hu ∣₁

        -- And conversely, into a PROPOSITION and never into data (trap T-E3,
        -- ledger clause L1). The target is an Ω and its isProp component is
        -- taken with snd, exactly as every PT.rec in Track B's file is.

        seam-active-out : (x n : S) (Q : Ω) → ⟨ seam-active x n ⟩
                        → ((b : S) (hb : ⟨ b ∈ˢ B ⟩) → ⟨ entry x b ∈ˢ n ⟩
                           → ⟨ U (b , hb) ⟩ → ⟨ Q ⟩)
                        → ⟨ Q ⟩
        seam-active-out x n Q h f =
          PT.rec (snd Q) (λ { (b , hb , he , hu) → f b hb he hu }) h

--------------------------------------------------------------------------------
-- The theorem, at K3's own value relation
--------------------------------------------------------------------------------

        -- The two activity bullets stay abstract here; K5/RoundTripAtUof.agda
        -- is the seam that fills them from Track D's Uof and measures their
        -- cost. Splitting the two seams keeps each file at one supplier and
        -- keeps this one at the single heavy module application rule 10
        -- budgets for this track.

        module Round
          (U-to-below   : (b : Pt B) → ⟨ U b ⟩
                        → ⟨ ⋁ RT.Cond (λ q → (fst q ∈ˢ below b) ⊓ U (RT.iPt q)) ⟩)
          (U-from-below : (b : Pt B) (q : RT.Cond) → ⟨ fst q ∈ˢ below b ⟩
                        → ⟨ U (RT.iPt q) ⟩ → ⟨ U b ⟩)
          where

          open RT.Value U seam-≈ seam-active seam-≈-intro
                          seam-active-in seam-active-out
                          U-to-below U-from-below
            public using ( ext-onto-raw )

          -- Printed at K3's relation, with no parameter left standing between
          -- the statement and Valuation.agda's own definition.

          round-trip : (n : S) → ⟨ Uv._≈[G]_ (trᴮ (trᴾ n)) n ⟩
          round-trip = ext-onto-raw

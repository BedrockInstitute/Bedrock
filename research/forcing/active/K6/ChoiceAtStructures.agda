{-# OPTIONS --cubical --safe --guardedness #-}

-- K6 Track I, seam probe. THE STRUCTURE IDENTITY CHECK, AND THE ASSEMBLED
-- RECORD AT K5's OWN STRUCTURE.
--
-- K6/Choice.agda does not apply K5.Structures. It builds the extension
-- structure as a record value out of the flat spine, which is what Part 4.0
-- requires of every K6 file outside a seam probe. That leaves one question no
-- body level grep can answer and no type error in K6/Choice.agda can raise:
--
--   IS THE OBJECT THE ASSEMBLED RECORD IS ABOUT THE OBJECT K5 BUILT?
--
-- A ZF record assembled at a REBUILT lookalike structure is a well typed
-- theorem about nothing. Track B named this on itself and discharged it by
-- refl (K6/ElementaryAtStructures.agda:141), Track F likewise
-- (K6/SeparationAtStructure.agda:111), and Track C likewise. This file is
-- Track I's, and it asks the question twice: once at the structure and once at
-- the assembled record's RESULT TYPE, which is the form that actually protects
-- a consumer.
--
-- Nothing is proved here. Every declaration is refl, a projection, or a
-- forwarded parameter.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import Valuation
import OrdinaryProfile
import K4.Algebra
import K5.Structures
import K6.Choice
import Cubical.HITs.PropositionalTruncation as PT

module K6.ChoiceAtStructures {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import FOL.Manipulation.ConstantOccurrences using ( countFo )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Induction.WellFounded using ( WellFounded )
open PT using ( ∥_∥₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

private module VL = Valuation 𝒮
open VL using ( Conditions )

open K4.Algebra 𝒮 using ( Pt )

-- The kernel telescope and the poset telescope, character for character from
-- K5/Structures.agda:209-217 and :777-784.

module Seam
  (entry       : S → S → S)
  (Child       : S → S → Type ℓ)
  (isPropChild : (x n : S) → isProp (Child x n))
  (child-entry : (x b n : S) → ⟨ entry x b ∈ˢ n ⟩ → Child x n)
  (child-wf    : WellFounded Child)
  (∅ᴺ          : S)
  (∅ᴺ-spec     : (z : S) → (z ∈ˢ ∅ᴺ) ≡ ⊥)
  (carrierᶠ    : S)
  (_≼ᶜ_        : Conditions carrierᶠ → Conditions carrierᶠ → Ω)
  (≼ᶜ-refl     : (p : Conditions carrierᶠ) → ⟨ p ≼ᶜ p ⟩)
  (≼ᶜ-trans    : {p q r : Conditions carrierᶠ} → ⟨ p ≼ᶜ q ⟩ → ⟨ q ≼ᶜ r ⟩ → ⟨ p ≼ᶜ r ⟩)
  (inhabitedᶜ  : ∥ Conditions carrierᶠ ∥₁)
  (IsNameᴾ     : S → Ω)
  (child-nameᴾ : (n : S) → ⟨ IsNameᴾ n ⟩ → (x : S) → Child x n → ⟨ IsNameᴾ x ⟩)
  where

  private
    module KS = K5.Structures.Kernel 𝒮
                  entry Child isPropChild child-entry child-wf ∅ᴺ ∅ᴺ-spec
    module PS = KS.PosetSide carrierᶠ _≼ᶜ_ ≼ᶜ-refl ≼ᶜ-trans inhabitedᶜ
                  IsNameᴾ child-nameᴾ
    module CH = K6.Choice 𝒮

  module At (G : PS.P.Sub)
    (Dense      : S → Ω)
    (DenseBelow : Conditions carrierᶠ → S → Ω)
    where

    private module E = PS.P.Ext G

    open E using ( Active ; ‖Active‖ ; active-child ; active-value ; entry-value
                 ; _≈[G]_ ; _∈[G]_ ; ≈-refl ; ≈-sym ; ≈-trans
                 ; ∈-congˡ ; ∈-congʳ )

    -- The three spine entries K6/Choice.agda states abstractly, discharged
    -- against K3's own definitions. The first is refl: _∈[G]_ IS the join over
    -- the active entries (Valuation.agda:294-295).

    ∈-unfold : (m n : S) → (m ∈[G] n) ≡ ⋁ S (λ y → ‖Active‖ y n ⊓ (m ≈[G] y))
    ∈-unfold m n = refl

    -- An active entry names a CONDITION in G together with its membership.
    -- This is Valuation.agda:245-247 repackaged, with the pair reassociated
    -- into K3's own Conditions type. Nothing is eliminated into data: the
    -- source is a truncation and so is the target.

    active-cond : (x n : S) → ⟨ ‖Active‖ x n ⟩
                → ⟨ ⋁ (Conditions carrierᶠ) (λ p → (G p) ⊓ (entry x (fst p) ∈ˢ n)) ⟩
    active-cond x n = PT.map step
      where
      step : Active x n
           → Σ[ p ∈ Conditions carrierᶠ ] ⟨ (G p) ⊓ (entry x (fst p) ∈ˢ n) ⟩
      step (p , hp , mem , hG) = (p , hp) , hG , mem

    entry-valueᶜ : (n x : S) (p : Conditions carrierᶠ) → ⟨ G p ⟩
                 → ⟨ entry x (fst p) ∈ˢ n ⟩ → ⟨ x ∈[G] n ⟩
    entry-valueᶜ n x p hG mem = entry-value n x (fst p) (snd p) hG mem

    module C = CH.At carrierᶠ IsNameᴾ Child child-nameᴾ entry G
                 _≼ᶜ_ ≼ᶜ-refl ≼ᶜ-trans _≈[G]_ _∈[G]_ ‖Active‖
                 ∈-unfold active-child active-value active-cond entry-valueᶜ
                 ≈-refl ≈-sym ≈-trans ∈-congˡ ∈-congʳ Dense DenseBelow

    --------------------------------------------------------------------------
    -- CHECK ONE. The carrier and the structure
    --------------------------------------------------------------------------

    carrier-agrees : C.Nm ≡ PS.Nameᴾ
    carrier-agrees = refl

    structure-agrees : C.𝒮ᴾ ≡ PS.𝒮ᴾ[ G ]
    structure-agrees = refl

    -- K5's own proved field, at K6's spelling of the structure. If the two
    -- structures were merely isomorphic rather than identical this line would
    -- not typecheck, and K6 would be re-proving Extensionality, which 2.0
    -- forbids in any form.

    ext[G] : OrdinaryProfile.Extensionality C.𝒮ᴾ
    ext[G] = PS.ext[ G ]

    --------------------------------------------------------------------------
    -- CHECK TWO. The assembled record's RESULT TYPE, at K5's structure
    --------------------------------------------------------------------------

    -- This is the check that protects a consumer. zf-at below is declared with
    -- its result written at PS.𝒮ᴾ[ G ], K5's own object, and filled by
    -- K6/Choice.agda's assembly, which was built at C.𝒮ᴾ. The eight producers
    -- arrive as parameters typed at K5's structure as well, so a lookalike
    -- anywhere in the chain fails here rather than shipping.

    module Assembly
      (B             : S)
      (IsNameᴮ       : S → Ω)
      (_≈ᵁ_ _∈ᵁ_     : CH.NameOf IsNameᴮ → CH.NameOf IsNameᴮ → Ω)
      (Uof           : Pt B → Ω)
      (eqᴬ memᴬ      : S → S → Pt B)
      (trᴮ           : S → S)
      (_≈[U]_        : S → S → Ω)
      (Supply        : ∀ {k} → CH.Src k → Type (ℓ-suc ℓ))
      (srcOf         : ∀ {k} (φ : Formula PS.Nameᴾ k) → CH.Src (k + countFo φ))
      (CompilerSurface FrameData TranslationRest : Type (ℓ-suc ℓ))
      where

      module A = C.Assemble B IsNameᴮ _≈ᵁ_ _∈ᵁ_ Uof eqᴬ memᴬ trᴮ _≈[U]_
                   Supply srcOf CompilerSurface FrameData TranslationRest

      module Producers
        (extensional : OrdinaryProfile.Extensionality PS.𝒮ᴾ[ G ])
        (pair        : ⟨ A.Positive ⟩ → OrdinaryProfile.Pairing PS.𝒮ᴾ[ G ])
        (union       : A.Upward → A.Directed → OrdinaryProfile.Union PS.𝒮ᴾ[ G ])
        (infinity    : ⟨ A.Positive ⟩ → OrdinaryProfile.Infinity PS.𝒮ᴾ[ G ])
        (found       : OrdinaryProfile.FoundationInduction PS.𝒮ᴾ[ G ])
        (separation  : A.Atom∈ → A.Atom≐ → CompilerSurface → FrameData
                     → TranslationRest → A.ExtSurjective → A.SupplyAll → LEM ℓ
                     → ⟨ A.Positive ⟩ → A.Upward → A.Directed → A.Meets
                     → OrdinaryProfile.Separation PS.𝒮ᴾ[ G ])
        (power       : A.Atom∈ → A.Atom≐ → CompilerSurface → FrameData
                     → TranslationRest → A.ExtSurjective → A.SupplyAll → LEM ℓ
                     → ⟨ A.Positive ⟩ → A.Upward → A.Directed → A.Meets
                     → OrdinaryProfile.PowerSet PS.𝒮ᴾ[ G ])
        (replacement : A.Atom∈ → A.Atom≐ → CompilerSurface → FrameData
                     → TranslationRest → A.ExtSurjective → A.SupplyAll → LEM ℓ
                     → ⟨ A.Positive ⟩ → A.Upward → A.Directed → A.Meets
                     → OrdinaryProfile.Collection PS.𝒮ᴾ[ G ])
        where

        module F = A.Fields extensional pair union infinity found
                     separation power replacement

        zf-at : A.Atom∈ → A.Atom≐ → CompilerSurface → FrameData
              → TranslationRest → A.ExtSurjective → A.SupplyAll → LEM ℓ
              → ⟨ A.Positive ⟩ → A.Upward → A.Directed → A.Meets
              → OrdinaryProfile.OrdinaryZF PS.𝒮ᴾ[ G ]
        zf-at = F.zfᴾ

        -- And the outer record, with Choice as a ninth argument and the ground
        -- well ordering opaque. Compare the two signatures: zf-at does not
        -- mention GroundWellOrder and cannot be made to.

        module WithChoiceAt
          (GroundWellOrder : Type (ℓ-suc ℓ))
          (choice : A.Atom∈ → A.Atom≐ → CompilerSurface → FrameData
                  → TranslationRest → A.ExtSurjective → A.SupplyAll → LEM ℓ
                  → ⟨ A.Positive ⟩ → A.Upward → A.Directed → A.Meets
                  → GroundWellOrder → OrdinaryProfile.ChoiceSet PS.𝒮ᴾ[ G ])
          where

          module W = F.WithChoice GroundWellOrder choice

          zfc-at : A.Atom∈ → A.Atom≐ → CompilerSurface → FrameData
                 → TranslationRest → A.ExtSurjective → A.SupplyAll → LEM ℓ
                 → ⟨ A.Positive ⟩ → A.Upward → A.Directed → A.Meets
                 → GroundWellOrder → OrdinaryProfile.OrdinaryZFC PS.𝒮ᴾ[ G ]
          zfc-at = W.zfcᴾ

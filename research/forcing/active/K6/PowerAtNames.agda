{-# OPTIONS --cubical --safe --guardedness #-}

-- K6 Track G's seam probe. The ONLY file of this track that applies
-- K5.Structures, per Part 4 of the architecture.
--
-- WHAT IT CHECKS. K6/Power.agda builds the extension structure as a record
-- literal from flat spine parameters rather than by applying K5.Structures,
-- so the one thing a reader cannot take on trust is that the literal is the
-- SAME structure. Every alias below has the K6 side's type written out and
-- the K5 side's term as its body, or is a refl between the two. A drift in
-- any of them fails here and not silently downstream.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
open import FOL.Syntax
open import Cubical.Induction.WellFounded using ( WellFounded )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ ; ∣_∣₁ )
import OrdinaryProfile
import Valuation
import K5.Structures
import K6.Power

module K6.PowerAtNames
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  where

open import FOL.ZFStructure using ( module hPropStructure )
open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

module Kernel
  (entry       : S → S → S)
  (entry-inj   : {x b y c : S} → entry x b ≡ entry y c → (x ≡ y) × (b ≡ c))
  (Child       : S → S → Type ℓ)
  (child-weight : (x n : S) → Child x n → ∥ Σ[ b ∈ S ] ⟨ entry x b ∈ˢ n ⟩ ∥₁)
  (isPropChild : (x n : S) → isProp (Child x n))
  (child-entry : (x b n : S) → ⟨ entry x b ∈ˢ n ⟩ → Child x n)
  (child-wf    : WellFounded Child)
  (∅ᴺ          : S)
  (∅ᴺ-spec     : (z : S) → (z ∈ˢ ∅ᴺ) ≡ ⊥)
  (carrierᶠ    : S)
  (_≼ᶜ_        : Valuation.Conditions 𝒮 carrierᶠ
               → Valuation.Conditions 𝒮 carrierᶠ → Ω)
  (≼ᶜ-refl     : (p : Valuation.Conditions 𝒮 carrierᶠ) → ⟨ p ≼ᶜ p ⟩)
  (≼ᶜ-trans    : {p q r : Valuation.Conditions 𝒮 carrierᶠ}
               → ⟨ p ≼ᶜ q ⟩ → ⟨ q ≼ᶜ r ⟩ → ⟨ p ≼ᶜ r ⟩)
  (inhabitedᶜ  : ∥ Valuation.Conditions 𝒮 carrierᶠ ∥₁)
  (IsNameᴾ     : S → Ω)
  (child-nameᴾ : (n : S) → ⟨ IsNameᴾ n ⟩ → (x : S) → Child x n → ⟨ IsNameᴾ x ⟩)
  (paths       : (x y : S) → (x ≈ˢ y) ≡ ((x ≡ y) , isSetS x y))
  where

  module K5S = K5.Structures.Kernel 𝒮
                 entry Child isPropChild child-entry child-wf ∅ᴺ ∅ᴺ-spec
  module PS  = K5S.PosetSide carrierᶠ _≼ᶜ_ ≼ᶜ-refl ≼ᶜ-trans inhabitedᶜ
                 IsNameᴾ child-nameᴾ
  module K6K = K6.Power.Kernel 𝒮 entry entry-inj Child child-weight
                 carrierᶠ IsNameᴾ child-nameᴾ paths

  -- Slot one. The condition type and the name type. Both by refl: K6/Power's
  -- Cond is Valuation.agda:121-122 and its Nameᴾ is K5/Structures.agda:259-260.

  cond-agrees : K6K.Cond ≡ PS.P.Cond
  cond-agrees = refl

  name-agrees : K6K.Nameᴾ ≡ PS.Nameᴾ
  name-agrees = refl

  module At (G : PS.P.Sub) where

    module EX = PS.P.Ext G
    module K6A = K6K.At G EX._≈[G]_ EX._∈[G]_

    -- Slot two. The activity predicate K6/Power writes out is K5's, which is
    -- what makes the ∈-unfold parameter below fillable at all.

    active-agrees : (x n : S) → K6A.‖Active‖ x n ≡ EX.‖Active‖ x n
    active-agrees x n = refl

    -- Slot three, THE LOAD-BEARING ONE. The record literal in K6/Power.agda
    -- is the structure K5 ships.

    structure-agrees : K6A.𝒮ᴾ ≡ PS.𝒮ᴾ[ G ]
    structure-agrees = refl

    -- Slot four. Consequently the field type K6 lands is the field type the
    -- consumer asks for, at the K5 structure and not at a look-alike.

    field-agrees : OrdinaryProfile.PowerSet K6A.𝒮ᴾ
                 ≡ OrdinaryProfile.PowerSet PS.𝒮ᴾ[ G ]
    field-agrees = refl

    -- Slot five. The eight value laws K6/Power.Kernel.At.Laws asks for are
    -- K5's own re-exports, each with the consumer's type written out and the
    -- producer's export as the body. This is the K5/ClausesAtFrame.agda shape.

    module Filled = K6A.Laws
      EX.≈-sym EX.≈-trans EX.∈-congˡ EX.value-extensional
      (λ m n → refl) EX.active-child EX.active-value EX.entry-value

    -- Slot six. Positivity, the ONLY hypothesis K6/Power charges on G. K5's
    -- filter projects to it, so a consumer holding a filter loses nothing.

    pos-from-filter : PS.P.isFilter G → ⟨ ⋁ K6K.Cond (λ q → G q) ⟩
    pos-from-filter = PS.P.filter-positive

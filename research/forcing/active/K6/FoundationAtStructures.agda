{-# OPTIONS --cubical --safe --guardedness #-}

-- K6 Track D, seam probe. One application of K5.Structures.Kernel.PosetSide,
-- and the `foundation` field asked for at the REAL _⊨_ of the extension
-- structure rather than at the flat parameters K6/Foundation.agda proves it
-- against.
--
-- Two results are asked for here and they are deliberately the same term at two
-- different spellings of one type.
--
--   foundation      : OrdinaryProfile.FoundationInduction 𝒮ᴾ[ G ]
--       the eighth field of OrdinaryZF (OrdinaryProfile.agda:126-135), at the
--       extension structure, for an ARBITRARY G : P.Sub. There is no
--       hypothesis on G anywhere in this file.
--
--   nonclaim3-holds : P.Ext.Founded G
--       K5's own type from K5/Structures.agda:519-520, the one shipped with
--       NON-CLAIM 3 and with no inhabitant. Inhabiting it by name is what makes
--       the correction of that non-claim machine checked rather than argued.
--
-- Nothing in this file inducts on, or assumes accessibility for, the
-- extension's membership. The only well founded relation named is Child, and it
-- is passed straight through as the parameter it arrives as.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import Valuation
import OrdinaryProfile
import K5.Structures
import K6.Foundation
import Cubical.HITs.PropositionalTruncation as PT

module K6.FoundationAtStructures {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import Cubical.Induction.WellFounded using ( WellFounded )
open PT using ( ∥_∥₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

private module VL = Valuation 𝒮
open VL using ( Conditions )

-- The kernel telescope and the poset telescope, character for character from
-- K5/Structures.agda:209-217 and :777-784, which is the same telescope
-- K5/ExtensionSat.agda:108-125 carries.

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
    module FD = K6.Foundation 𝒮

  module At (G : PS.P.Sub) where

    private module E = PS.P.Ext G

    open E using ( _≈[G]_ ; _∈[G]_ ; ‖Active‖ ; active-child ; ≈-refl ; ≈-sym
                 ; _⊨_ ; Agree ; sat-cong )

    -- The unfolding law of the spine, discharged by reflexivity: _∈[G]_ IS the
    -- join over the active entries (Valuation.agda:294-295).

    ∈-unfold : (m n : S) → (m ∈[G] n) ≡ ⋁ S (λ y → ‖Active‖ y n ⊓ (m ≈[G] y))
    ∈-unfold m n = refl

    -- The one parameter beyond the shared spine, discharged in two clauses over
    -- K5's concrete Agree (K5/Structures.agda:376-377). This is the poset side
    -- of the helper K5 already wrote for the Boolean side at
    -- K5/ExtensionSat.agda:159-162.

    consᴾ : ∀ {k} (σ τ : PS.P.Nm) (μ : Vec PS.P.Nm k) → ⟨ fst σ ≈[G] fst τ ⟩
          → Agree (σ ∷ μ) (τ ∷ μ)
    consᴾ σ τ μ h zero     = h
    consᴾ σ τ μ h (suc ix) = ≈-refl (fst (lookup ix μ))

    agree-head : (σ τ : PS.P.Nm) → ⟨ fst σ ≈[G] fst τ ⟩
               → Agree (σ ∷ []) (τ ∷ [])
    agree-head σ τ h = consᴾ σ τ [] h

    private
      module D = FD.At Child child-wf IsNameᴾ child-nameᴾ
                   _≈[G]_ _∈[G]_ ‖Active‖ ∈-unfold active-child ≈-sym
                   _⊨_ Agree agree-head sat-cong

    -- The field, at the profile's own type.

    foundation : OrdinaryProfile.FoundationInduction PS.𝒮ᴾ[ G ]
    foundation = D.foundation

    -- K5's NON-CLAIM 3, inhabited by name.

    nonclaim3-holds : PS.P.Ext.Founded G
    nonclaim3-holds = D.foundation

{-# OPTIONS --cubical --safe --guardedness #-}

-- K6 Track B, seam probe, K5 half. One application of
-- K5.Structures.Kernel.PosetSide, and `hasPair` and `hasUnion` asked for at
-- OrdinaryProfile's own types over the REAL extension structure 𝒮ᴾ[ G ] rather
-- than over the record K6/Elementary.agda rebuilds from the flat spine.
--
-- The one identification this file exists to check is `structure-agrees`: that
-- the structure Track B proves its two fields at IS K5's 𝒮ᴾ[ G ], by refl. A
-- Pairing proved at a different structure is a well typed theorem about
-- nothing, and no grep over K6/Elementary.agda could see the difference.
--
-- Two of the flat spine's parameters are discharged here by reflexivity, which
-- is the measured claim that they are K3's defining equations and not
-- assumptions: `∈-unfold` (Valuation.agda:294-295) and `active-spec`
-- (Valuation.agda:245-250).
--
-- Track A's five exports stay parameters HERE. Their types are
-- K6/NameBuild.agda:294-300 and :348-353 and K6/NameValid.agda:144-148 with the
-- ground axioms `coll` and `sep` partially applied; filling them from the real
-- K6.NameBuild and K6.NameValid is the remaining half of the probe and is
-- K6/ElementaryAtNames.agda.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import Valuation
import OrdinaryProfile
import CodedVocabulary
import K5.Structures
import K6.Elementary
import Cubical.HITs.PropositionalTruncation as PT

module K6.ElementaryAtStructures {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import Cubical.Induction.WellFounded using ( WellFounded )
open import Cubical.Data.Sigma using ( _×_ )
open PT using ( ∥_∥₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

private module VL = Valuation 𝒮
open VL using ( Conditions )

open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
open At S id using ( _⊨_ )

open import CodedVocabulary 𝒮 using ( isKPairΔ ; refinesΔ )

module Seam
  -- K5/Structures.agda:209-217, character for character.
  (entry       : S → S → S)
  (Child       : S → S → Type ℓ)
  (isPropChild : (x n : S) → isProp (Child x n))
  (child-entry : (x b n : S) → ⟨ entry x b ∈ˢ n ⟩ → Child x n)
  (child-wf    : WellFounded Child)
  (∅ᴺ          : S)
  (∅ᴺ-spec     : (z : S) → (z ∈ˢ ∅ᴺ) ≡ ⊥)
  -- K5/Structures.agda:777-784, character for character.
  (carrierᶠ    : S)
  (_≼ᶜ_        : Conditions carrierᶠ → Conditions carrierᶠ → Ω)
  (≼ᶜ-refl     : (p : Conditions carrierᶠ) → ⟨ p ≼ᶜ p ⟩)
  (≼ᶜ-trans    : {p q r : Conditions carrierᶠ} → ⟨ p ≼ᶜ q ⟩ → ⟨ q ≼ᶜ r ⟩ → ⟨ p ≼ᶜ r ⟩)
  (inhabitedᶜ  : ∥ Conditions carrierᶠ ∥₁)
  (IsNameᴾ     : S → Ω)
  (child-nameᴾ : (n : S) → ⟨ IsNameᴾ n ⟩ → (x : S) → Child x n → ⟨ IsNameᴾ x ⟩)
  -- K3's two facts about the entry, NameKernel.agda:321 and :332, K3's
  -- determinacy NameSupport.agda:486, and the ground's equality as a path.
  (entry-inj     : {x b y c : S} → entry x b ≡ entry y c → (x ≡ y) × (b ≡ c))
  (entry-isKPair : (x b : S) → ⟨ isKPairΔ (entry x b) x b ⟩)
  (kpair-unique  : (q x b : S) → ⟨ isKPairΔ q x b ⟩ → q ≡ entry x b)
  (paths         : (x y : S) → (x ≈ˢ y) ≡ ((x ≡ y) , isSetS x y))
  -- The coded order graph, CodedCompletion.agda:218-219 and :241.
  (order     : S)
  (≼-reading : (p q : Conditions carrierᶠ)
             → (p ≼ᶜ q) ≡ refinesΔ order (fst p) (fst q))
  -- Two ground terms, NameKernel.agda:204-207 and NameSupport.agda:444-450, :465.
  (pairOf        : S → S → S)
  (pairOf-spec   : (a b x : S) → (x ∈ˢ pairOf a b) ≡ ((x ≈ˢ a) ⊔ (x ≈ˢ b)))
  (⋃ᴳ            : S → S)
  (⋃ᴳ-in         : (a y x : S) → ⟨ y ∈ˢ a ⟩ → ⟨ x ∈ˢ y ⟩ → ⟨ x ∈ˢ ⋃ᴳ a ⟩)
  (support-bound : (n x b : S) → ⟨ entry x b ∈ˢ n ⟩ → ⟨ x ∈ˢ ⋃ᴳ (⋃ᴳ n) ⟩)
  -- Track A, K6/NameBuild.agda and K6/NameValid.agda, with coll and sep applied.
  (entryBound      : S → S)
  (entryBound-spec : (D e : S) → (e ∈ˢ entryBound D)
                   ≡ ⋁ S (λ x → (x ∈ˢ D)
                        ⊓ ⋁ S (λ p → (p ∈ˢ carrierᶠ) ⊓ (e ≈ˢ entry x p))))
  (mk              : S → Formula S 1 → S)
  (mk-spec         : (bound : S) (θ : Formula S 1) (e : S)
                   → (e ∈ˢ mk bound θ)
                   ≡ ((e ∈ˢ bound) ⊓ ((e ∷ []) ⊨ θ)))
  (mk-name         : (bound : S) (θ : Formula S 1)
                   → ((e : S) → ⟨ e ∈ˢ mk bound θ ⟩
                      → ∥ Σ[ x ∈ S ] Σ[ p ∈ S ]
                           ((e ≡ entry x p)
                            × (⟨ p ∈ˢ carrierᶠ ⟩ × ⟨ IsNameᴾ x ⟩)) ∥₁)
                   → ⟨ IsNameᴾ (mk bound θ) ⟩)
  where

  private
    module KS = K5.Structures.Kernel 𝒮
                  entry Child isPropChild child-entry child-wf ∅ᴺ ∅ᴺ-spec
    module PS = KS.PosetSide carrierᶠ _≼ᶜ_ ≼ᶜ-refl ≼ᶜ-trans inhabitedᶜ
                  IsNameᴾ child-nameᴾ
    module EL = K6.Elementary 𝒮

  module AtG (G : PS.P.Sub) where

    private module E = PS.P.Ext G

    open E using ( _≈[G]_ ; _∈[G]_ ; ‖Active‖ ; entry-value
                 ; ≈-refl ; ≈-sym ; ∈-congˡ ; ∈-congʳ )

    -- The two defining equations of K3's value layer, discharged by
    -- reflexivity. This is the whole content of the claim that the flat spine
    -- constrains its two abstract relations rather than assuming anything
    -- about them.

    ∈-unfold : (m n : S) → (m ∈[G] n) ≡ ⋁ S (λ y → ‖Active‖ y n ⊓ (m ≈[G] y))
    ∈-unfold m n = refl

    active-spec : (x n : S) → ‖Active‖ x n
                ≡ ( ∥ Σ[ p ∈ S ] Σ[ hp ∈ ⟨ p ∈ˢ carrierᶠ ⟩ ]
                        (⟨ entry x p ∈ˢ n ⟩ × ⟨ G (p , hp) ⟩) ∥₁ , PT.squash₁ )
    active-spec x n = refl

    private
      module B = EL.Build paths entry entry-inj entry-isKPair kpair-unique
                   Child child-entry carrierᶠ _≼ᶜ_ order ≼-reading
                   IsNameᴾ child-nameᴾ G _≈[G]_ _∈[G]_ ‖Active‖
                   active-spec ∈-unfold entry-value ≈-refl ≈-sym
                   ∈-congˡ ∈-congʳ entryBound entryBound-spec mk mk-spec
                   mk-name pairOf pairOf-spec ⋃ᴳ ⋃ᴳ-in support-bound

    -- THE IDENTIFICATION. The structure Track B proves its two fields at is
    -- K5's own 𝒮ᴾ[ G ], on the nose.

    structure-agrees : B.structureᴱ ≡ PS.𝒮ᴾ[ G ]
    structure-agrees = refl

    -- The two fields, at the profile's own types over K5's structure. The
    -- hypotheses are the MEASURED ones: positivity for Pairing, upward closure
    -- and directedness for Union, and no others.

    hasPair : ⟨ PS.P.positive G ⟩ → OrdinaryProfile.Pairing PS.𝒮ᴾ[ G ]
    hasPair = B.hasPairᴾ

    hasUnion : B.Upward → B.Directed → OrdinaryProfile.Union PS.𝒮ᴾ[ G ]
    hasUnion = B.hasUnionᵁᴰ

    -- The architecture's own spelling, through K5's re-exported isFilter and
    -- filter-positive, which is what the ledger row is derived from.

    hasPairᶠ : PS.P.isFilter G → OrdinaryProfile.Pairing PS.𝒮ᴾ[ G ]
    hasPairᶠ fil = B.hasPairᴾ (PS.P.filter-positive fil)

    hasUnionᶠ : PS.P.isFilter G → OrdinaryProfile.Union PS.𝒮ᴾ[ G ]
    hasUnionᶠ fil = B.hasUnionᵁᴰ (PS.P.isFilter.upward fil)
                                 (PS.P.isFilter.directed fil)

    -- The content theorems, asked for at variable names, which is what the
    -- architecture's Track B seam probe requires: the membership statement of
    -- the constructed pair, and of the constructed union, at arbitrary σ, τ.

    pair-mem : ⟨ PS.P.positive G ⟩ → (σ τ : PS.P.Nm) (χ : S)
             → (χ ∈[G] B.pairCode (fst σ) (fst τ))
             ≡ ((χ ≈[G] fst σ) ⊔ (χ ≈[G] fst τ))
    pair-mem pos σ τ = B.pair-mem pos (fst σ) (fst τ)

    union-mem : B.Upward → B.Directed → (τ : PS.P.Nm) (χ : S)
              → (χ ∈[G] B.unionCode (fst τ))
              ≡ ⋁ S (λ y → (y ∈[G] fst τ) ⊓ (χ ∈[G] y))
    union-mem = B.union-mem

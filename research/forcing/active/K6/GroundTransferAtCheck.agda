{-# OPTIONS --cubical --safe --guardedness #-}

-- K6 Track C, supplier probe. This file answers one question and proves no
-- theorem: ruling D3 makes chk, chk-spec, chk-name, Γ and Γ-spec parameters
-- of Track C, and rule 15 asks whether an inhabitant of that telescope exists
-- at a genuine forcing extension, or whether the ruling has quietly turned an
-- unprovable statement into a convenience.
--
-- It exists, it is K3's, and the compiler agrees below. StandardNames builds
-- the poset check name by host well-founded recursion on the GROUND's
-- membership (StandardNames.agda:319-320, with the propositional computation
-- law at :322-323), derives its membership specification at :331-332, its
-- validity at :391-392, and the generic name and its specification at
-- :616-621. This file takes that module's own telescope, applies it, and
-- feeds the five results into Track C's module Copy by name.
--
-- WHAT THE SUPPLIER COSTS, which is the ledger row and is visible here as a
-- telescope rather than asserted in prose. StandardNames.agda:265-273 asks
-- for exactly three things beyond the name kernel:
--
--   * acc∈ : WellFounded _∈ᵗ_, tier 0. Well-foundedness of the GROUND's
--     membership. True at any transitive ground; it is the relation Bell's
--     1.21 recursion runs on. It is NOT the extension's membership, whose
--     well-foundedness Bell makes equivalent to genericity.
--   * image and image-spec, tier 4, K3's MemberImage. This is obstruction
--     O3b, undischarged at L, and StandardNames.agda:52-54 states the joint
--     dependence in terms: tier 4 "is not derivable from any first-order
--     axiom, it is load bearing jointly with tier 0, and neither alone
--     produces check".
--   * unionOf and unionOf-spec, tier 2, the ground's Union, charged by the
--     poset side only.
--
-- So Track C's open row is a COST with a named supplier and a named price,
-- and not an impossibility. The one thing that is impossible at this layer is
-- the INTERNAL image form of the same datum, for the reason
-- NameImage.agda:392-400 gives.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import StandardNames
import K6.GroundTransfer
import Cubical.HITs.PropositionalTruncation as PT

module K6.GroundTransferAtCheck {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import Cubical.Induction.WellFounded using ( WellFounded )
open import Cubical.Data.Sigma using ( _×_ ; _,_ )
open PT using ( ∥_∥₁ ; ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

module Supplier
  (entry           : S → S → S)
  (entry-inj       : {x b y c : S} → entry x b ≡ entry y c → (x ≡ y) × (b ≡ c))
  (singleOf        : S → S)
  (singleOf-spec   : (a z : S) → ⟨ z ∈ˢ singleOf a ⟩ → z ≡ a)
  (singleOf-member : (a : S) → ⟨ a ∈ˢ singleOf a ⟩)
  (Child           : S → S → Type ℓ)
  (child-elim      : (x n : S) (Q : Ω) → Child x n
                   → ((b : S) → ⟨ entry x b ∈ˢ n ⟩ → ⟨ Q ⟩) → ⟨ Q ⟩)
  (≈ˢ-paths        : (x y : S) → (x ≈ˢ y) ≡ ((x ≡ y) , isSetS x y))
  (ext-path        : {a b : S} → ((x : S) → (x ∈ˢ a) ≡ (x ∈ˢ b)) → a ≡ b)
  (acc∈            : WellFounded _∈ᵗ_)
  (image           : (a : S) (f : (Σ[ x ∈ S ] ⟨ x ∈ˢ a ⟩) → S) → S)
  (image-spec      : (a : S) (f : (Σ[ x ∈ S ] ⟨ x ∈ˢ a ⟩) → S) (z : S)
                   → (z ∈ˢ image a f)
                   ≡ ⋁ S (λ x → ⋁ ⟨ x ∈ˢ a ⟩ (λ h → z ≈ˢ f (x , h))))
  (unionOf         : S → S)
  (unionOf-spec    : (t z : S) → (z ∈ˢ unionOf t)
                   ≡ ⋁ S (λ u → (u ∈ˢ t) ⊓ (z ∈ˢ u)))
  (carrierᶠ        : S)
  (IsNameᴾ         : S → Ω)
  (entries-nameᴾ   : (n : S)
                   → ((e : S) → ⟨ e ∈ˢ n ⟩
                      → ∥ Σ[ x ∈ S ] Σ[ b ∈ S ]
                          ((e ≡ entry x b) × (⟨ b ∈ˢ carrierᶠ ⟩ × ⟨ IsNameᴾ x ⟩)) ∥₁)
                   → ⟨ IsNameᴾ n ⟩)
  (_≈[G]_ _∈[G]_   : S → S → Ω)
  (Cond            : Type ℓ)
  (G               : Cond → Ω)
  where

  private
    module SK = StandardNames.Kernel 𝒮
                  entry entry-inj singleOf singleOf-spec singleOf-member
                  Child child-elim ≈ˢ-paths ext-path
    module SW = SK.Weighted acc∈ image image-spec unionOf unionOf-spec
    module Ps = SW.Over carrierᶠ
    module PsValid = Ps.Valid carrierᶠ IsNameᴾ entries-nameᴾ (λ p hp → hp)

  -- The generic name, StandardNames.agda:616-621 transcribed at this carrier.

  Γᴾ : S
  Γᴾ = SW.imageOn carrierᶠ (λ p → entry (Ps.chk p) p)

  Γᴾ-spec : (e : S) → (e ∈ˢ Γᴾ)
          ≡ ⋁ S (λ p → (p ∈ˢ carrierᶠ) ⊓ (e ≈ˢ entry (Ps.chk p) p))
  Γᴾ-spec = SW.imageOn-spec carrierᶠ (λ p → entry (Ps.chk p) p)

  -- The application. Every one of the five slots ruling D3 names is filled by
  -- a name, not by a lambda and not by a local definition. If any of the five
  -- types had drifted from K3's, this line would fail.

  module T = K6.GroundTransfer.Transfer 𝒮 IsNameᴾ _≈[G]_ _∈[G]_ Cond G
  module TC = T.Copy entry carrierᶠ Ps.chk Ps.chk-spec Γᴾ Γᴾ-spec PsValid.chk-name

  -- And the one thing the application buys on its own, with no positivity and
  -- no filter: the ground lands in the carrier of the extension structure.

  copy : S → T.Nm
  copy = TC.groundName

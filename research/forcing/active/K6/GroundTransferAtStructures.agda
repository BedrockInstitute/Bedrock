{-# OPTIONS --cubical --safe --guardedness #-}

-- K6 Track C, seam probe. Nothing is proved here. Every parameter of
-- K6.GroundTransfer is filled from K5.Structures by NAME, so a drift in any
-- one of them fails here rather than passing silently inside a file whose own
-- telescope is a set of variables. Three things this probe is aimed at:
--
--   * the Δ₀ certificate's constructor order and the two reading theorems.
--     Inside Track C's own file the formula and its readings are both local,
--     so an off-by-one in either bound would survive; here groundSat is K5's
--     and the readings are Track C's, and the two must meet.
--   * the identity of the extension structure. Track C assembles the
--     ZFStructure from the flat value relation so that satisfaction computes;
--     this probe asks Agda whether that assembly IS K5's, by requiring K5's
--     groundSat, stated at K5's own _⊨_, to fill Track C's slot, and by
--     asking for the delivered field at 𝒮ᴾ[ G ] rather than at a local copy.
--   * the hypothesis. hasInfinity is asked for at ⟨ P.positive G ⟩, the real
--     predicate of ForcingNotion, and not at Track C's spelling of it.
--
-- The telescope is K5's Kernel and PosetSide telescopes concatenated, exactly
-- as K5/ExtensionSat.agda:108-127 does it, plus K5's Copy telescope and the
-- ground's Infinity.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile
import Valuation
import K5.Structures
import K6.GroundTransfer
import Cubical.HITs.PropositionalTruncation as PT

module K6.GroundTransferAtStructures {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import Cubical.Induction.WellFounded using ( WellFounded )
open import Cubical.Data.Sigma using ( _×_ ; _,_ )
open import FOL.Manipulation.ConstantMapping using ( mapFo )
open PT using ( ∥_∥₁ ; ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

private module VL = Valuation 𝒮
open VL using ( Conditions )

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

  module AtG (G : PS.P.Sub)
    (entry-inj   : {x b y c : S} → entry x b ≡ entry y c → (x ≡ y) × (b ≡ c))
    (≈ˢ-paths    : (x y : S) → (x ≈ˢ y) ≡ ((x ≡ y) , isSetS x y))
    (ext-path    : {a b : S} → ((x : S) → (x ∈ˢ a) ≡ (x ∈ˢ b)) → a ≡ b)
    (chk         : S → S)
    (chk-spec    : (a e : S) → (e ∈ˢ chk a)
                 ≡ ⋁ S (λ y → (y ∈ˢ a) ⊓ ⋁ S (λ p → (p ∈ˢ carrierᶠ)
                        ⊓ (e ≈ˢ entry (chk y) p))))
    (Γ           : S)
    (Γ-spec      : (e : S) → (e ∈ˢ Γ)
                 ≡ ⋁ S (λ p → (p ∈ˢ carrierᶠ) ⊓ (e ≈ˢ entry (chk p) p)))
    (chk-name    : (a : S) → ⟨ IsNameᴾ (chk a) ⟩)
    (inf         : OrdinaryProfile.Infinity 𝒮)
    where

    private
      module E = PS.P.Ext G
      module C = E.Copy entry-inj ≈ˢ-paths ext-path chk chk-spec Γ Γ-spec chk-name

      module T = K6.GroundTransfer.Transfer 𝒮 IsNameᴾ E._≈[G]_ E._∈[G]_ PS.P.Cond G
      module TC = T.Copy entry carrierᶠ chk chk-spec Γ Γ-spec chk-name

    -- The one computation equation Track C asks for beyond K5's exports: the
    -- copied environment at arity one. K5's chkEnv is mapEnv groundName and
    -- the vector is concrete, so it reduces.

    chkEnv-one : (u : S) → C.chkEnv (u ∷ []) ≡ (TC.groundName u ∷ [])
    chkEnv-one u = refl

    private
      module TG = TC.Ground C.chkEnv chkEnv-one
                    C.WithPos.groundSat C.WithPos.check-value
                    C.WithPos.check-faithful C.WithPos.chk-≈ inf

    --------------------------------------------------------------------------
    -- The assertions
    --------------------------------------------------------------------------

    -- The structure Track C assembles IS the structure K5 exports.

    structure-is : T.𝒮ᴾ ≡ PS.𝒮ᴾ[ G ]
    structure-is = refl

    -- The delivered field, at the architecture's own signature: K5's
    -- structure, ForcingNotion's own positivity predicate, K1's own record
    -- field type. Nothing on either side of the colon is Track C's spelling.

    hasInfinity : ⟨ PS.P.positive G ⟩ → OrdinaryProfile.Infinity PS.𝒮ᴾ[ G ]
    hasInfinity = TG.hasInfinity

    -- The non-vacuity certificate, at the real value relation. An inhabitant
    -- of a join over the real Nm, produced from the ground's Infinity alone.

    nonvacuous : ⟨ PS.P.positive G ⟩
               → ⟨ ⋁ PS.Nameᴾ (λ υ → ⋁ PS.Nameᴾ (λ ε → fst ε E.∈[G] fst υ)) ⟩
    nonvacuous = TG.infinity-nonvacuous

    -- The naturals identification, at a ground ω supplied by the consumer.

    module AtOmega (ωᴳ : S) where

      private module A = TG.AtOmega ωᴳ

      nat-faithful : ⟨ PS.P.positive G ⟩ → (m n : S)
                   → (chk m E.∈[G] chk n) ≡ (m ∈ˢ n)
      nat-faithful = A.nat-faithful

      nat-onto : ⟨ PS.P.positive G ⟩ → (τ : S) → ⟨ τ E.∈[G] chk ωᴳ ⟩
               → ⟨ ⋁ S (λ n → (n ∈ˢ ωᴳ) ⊓ (τ E.≈[G] chk n)) ⟩
      nat-onto = A.nat-onto

      nat-inj : ⟨ PS.P.positive G ⟩ → (m n : S) → ⟨ chk m E.≈[G] chk n ⟩
              → ⟨ m ≈ˢ n ⟩
      nat-inj = A.nat-inj

      nat-cong : ⟨ PS.P.positive G ⟩ → (m n : S) → ⟨ m ≈ˢ n ⟩
               → ⟨ chk m E.≈[G] chk n ⟩
      nat-cong = A.nat-cong

    -- The two reading theorems, re-asked at the real satisfaction relation.
    -- E.Sat._⊨_ is K5's, not Track C's, and the equation is the same refl.

    read-extension : (σ : PS.Nameᴾ)
                   → E.Sat._⊨_ (σ ∷ []) (mapFo TC.groundName T.infFo)
                   ≡ T.infBodyᴾ σ
    read-extension σ = refl

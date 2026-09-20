{-# OPTIONS --cubical --safe --guardedness #-}

-- K6 Track F, the seam probe. It answers one question and it is the question
-- that decides whether K6/Separation.agda proves the field it claims to prove.
--
-- K6/Separation.agda does not apply K5.Structures. It builds the extension
-- structure itself, as a record VALUE with the four expressions
-- K5/Structures.agda:285-291 writes, over a carrier spelled the way
-- K5/Structures.agda:263-264 spells it. If that record is only PROPOSITIONALLY
-- equal to the landed one, then the satisfaction inside
-- OrdinaryProfile.Separation of it is a different function and the load
-- bearing identity of architecture section 4.0 does not hold there. The two
-- refl lines below are the discriminator: they pass exactly when the two
-- records, and hence the two Separation types, are DEFINITIONALLY the same.
--
-- Everything of Track A and Track E stays a parameter here, because neither
-- track has landed. What this file fills from K5 is the whole structure side:
-- the carrier, the two relations, the entry presentation of activity, the
-- unfolding of membership, and sat-cong.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
open import Cubical.Induction.WellFounded using ( WellFounded )
import OrdinaryProfile
import FOL.Semantics
import NameKernel
import K6.NameBuildAtGround
import Valuation
import K5.Structures
import K6.Separation
import Cubical.HITs.PropositionalTruncation as PT

open PT using ( ∥_∥₁; ∣_∣₁ )

module K6.SeparationAtStructure {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

open import FOL.Syntax using ( Formula )
open OrdinaryProfile 𝒮 using ( Separation; Collection )

private module SemG = FOL.Semantics (hPropAlgebra ℓ) 𝒮
open SemG.At S id using ( _⊨_ )

private module VL = Valuation 𝒮
open VL using ( Conditions )

private module NK = NameKernel 𝒮

module Probe
  (entry       : S → S → S)
  (Child       : S → S → Type ℓ)
  (isPropChild : (x n : S) → isProp (Child x n))
  (child-entry : (x b n : S) → ⟨ entry x b ∈ˢ n ⟩ → Child x n)
  (child-wf    : WellFounded Child)
  (∅ᴺ          : S)
  (∅ᴺ-spec     : (z : S) → (z ∈ˢ ∅ᴺ) ≡ ⊥)
  (carrierᶠ    : S)
  (_≼ᶠ_        : Conditions carrierᶠ → Conditions carrierᶠ → Ω)
  (≼ᶠ-refl     : (p : Conditions carrierᶠ) → ⟨ p ≼ᶠ p ⟩)
  (≼ᶠ-trans    : {p q r : Conditions carrierᶠ} → ⟨ p ≼ᶠ q ⟩ → ⟨ q ≼ᶠ r ⟩ → ⟨ p ≼ᶠ r ⟩)
  (inhabitedᶠ  : ∥ Conditions carrierᶠ ∥₁)
  (IsNm        : S → Ω)
  (child-name  : (n : S) → ⟨ IsNm n ⟩ → (x : S) → Child x n → ⟨ IsNm x ⟩)
  where

  module KS = K5.Structures.Kernel 𝒮
                entry Child isPropChild child-entry child-wf ∅ᴺ ∅ᴺ-spec
  module SD = KS.Side carrierᶠ _≼ᶠ_ ≼ᶠ-refl ≼ᶠ-trans inhabitedᶠ IsNm child-name

  module NM = K6.Separation.Names 𝒮 entry Child child-entry carrierᶠ IsNm child-name

  module At (G : SD.Sub) where

    module E = SD.Ext G

    -- The entry presentation of activity, in both directions. K3's Active is
    -- the Σ itself (Valuation.agda:245-247), so both directions are a
    -- reshuffle of the same four components and neither costs an axiom.

    active-out : (x n : S) → ⟨ E.‖Active‖ x n ⟩
               → ⟨ ⋁ SD.Cond (λ r → (r SD.∈ᴾ G) ⊓ (entry x (fst r) ∈ˢ n)) ⟩
    active-out x n = PT.map
      (λ { (p , hp , hmem , hG) → (p , hp) , hG , hmem })

    active-in : (x n : S) (r : SD.Cond) → ⟨ r SD.∈ᴾ G ⟩
              → ⟨ entry x (fst r) ∈ˢ n ⟩ → ⟨ E.‖Active‖ x n ⟩
    active-in x n r hG hmem = ∣ fst r , snd r , hmem , hG ∣₁

    -- Membership unfolds definitionally (Valuation.agda:294-295), which is the
    -- reason the consumer may take the unfolding as a path parameter and pay
    -- nothing for it here.

    ∈-unfold : (m n : S)
             → (m E.∈[G] n) ≡ ⋁ S (λ y → E.‖Active‖ y n ⊓ (m E.≈[G] y))
    ∈-unfold m n = refl

    module FA = NM.AtG SD.Cond fst snd (SD._∈ᴾ G)
                  E._≈[G]_ E._∈[G]_ E.‖Active‖
                  E.≈-sym E.∈-congˡ ∈-unfold E.active-value
                  active-out active-in

    ----------------------------------------------------------------------------
    -- THE TWO DISCRIMINATING LINES
    ----------------------------------------------------------------------------

    structure-is : FA.𝒮ᴱ ≡ E.structure
    structure-is = refl

    separation-is : FA.OP.Separation ≡ OrdinaryProfile.Separation E.structure
    separation-is = refl

    -- And the satisfaction the field quantifies over is the one K5 proves
    -- sat-cong about, again definitionally rather than up to a path.

    sat-is : ∀ {k} (ν : Vec NM.Nm k) (φ : _) → (FA._⊨_ ν φ) ≡ (E._⊨_ ν φ)
    sat-is ν φ = refl

    agree-is : ∀ {k} (ν μ : Vec NM.Nm k) → (FA.Agree ν μ) ≡ (E.Agree ν μ)
    agree-is ν μ = refl

    ----------------------------------------------------------------------------
    -- The consumer, with K5's sat-cong plugged in and Track A and Track E left
    -- open. A track that lands A and E fills the remaining fourteen slots and
    -- reads off OrdinaryProfile.Separation E.structure with no further work.
    ----------------------------------------------------------------------------

    module Consumer = FA.Cut E.sat-cong

--------------------------------------------------------------------------------
-- TRACK A, THE TYPE CHECK
--------------------------------------------------------------------------------

-- The consumer's seven Track A slots, declared with the types K6/Separation.agda
-- writes and inhabited by the landed exports. This is the drift check the
-- architecture asks every consuming track to run: a character level difference
-- between what Track F transcribed and what Track A shipped fails here, in
-- seven lines, rather than inside a proof. No mathematics.

module TrackA (𝔉 : NK.Families) (acc∈ : NK.Accessibility) (carrierᶠ : S) where

  module AG = K6.NameBuildAtGround.Seam 𝒮 𝔉 acc∈ carrierᶠ

  dom-is : S → S
  dom-is = AG.BG.support

  dom-in-is : (n : S) → ⟨ AG.K.IsName n ⟩ → (x : S) → AG.K.Child x n
            → ⟨ x ∈ˢ AG.BG.support n ⟩
  dom-in-is = AG.BG.support-in

  dom-out-is : (n x : S) → ⟨ x ∈ˢ AG.BG.support n ⟩ → AG.K.Child x n
  dom-out-is = AG.BG.support-out

  entryBound-is : Collection → Separation → (D : S) → S
  entryBound-is = AG.Build.entryBound

  entryBound-in-is : (coll : Collection) (sep : Separation) (D x p : S)
                   → ⟨ x ∈ˢ D ⟩ → ⟨ p ∈ˢ carrierᶠ ⟩
                   → ⟨ AG.K.entry x p ∈ˢ AG.Build.entryBound coll sep D ⟩
  entryBound-in-is = AG.Build.entryBound-in

  mk-is : Separation → (bound : S) → Formula S 1 → S
  mk-is = AG.Build.mk

  mk-in-is : (sep : Separation) (bound : S) (θ : Formula S 1) (e : S)
           → ⟨ e ∈ˢ bound ⟩ → ⟨ (e ∷ []) ⊨ θ ⟩
           → ⟨ e ∈ˢ AG.Build.mk sep bound θ ⟩
  mk-in-is = AG.Build.mk-in

  mk-sat-is : (sep : Separation) (bound : S) (θ : Formula S 1) (e : S)
            → ⟨ e ∈ˢ AG.Build.mk sep bound θ ⟩ → ⟨ (e ∷ []) ⊨ θ ⟩
  mk-sat-is = AG.Build.mk-sat

  cut-name-is : (coll : Collection) (sep : Separation) (D : S) (θ : Formula S 1)
              → ((x : S) → ⟨ x ∈ˢ D ⟩ → ⟨ AG.K.IsName x ⟩)
              → ⟨ AG.K.IsName
                    (AG.Build.mk sep (AG.Build.entryBound coll sep D) θ) ⟩
  cut-name-is = AG.Valid.cut-name

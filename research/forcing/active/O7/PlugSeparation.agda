{-# OPTIONS --cubical --safe --guardedness #-}

-- O7, THE AIRTIGHT DISCHARGE AT TRACK F.
--
-- The file O7/Definability.agda states the three projections at types written
-- out by hand. This file does not trust that transcription: it takes the WHOLE
-- telescope of K6.Separation's module Cut except its last two parameters,
-- applies the real module, and passes O7's sepΔ and sepΔ-reading into the two
-- slots K6 declared. If the produced datum had the wrong shape at any depth
-- this application would not elaborate.
--
-- Three parameters appear here that Track F's own telescope does NOT carry,
-- and they are the honest extra cost of SUPPLYING the datum rather than
-- consuming it: kpair-unique (NameSpace.agda:388), entry-inj
-- (NameKernel.agda:321) and, of course, the general datum itself.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
open import FOL.Syntax using ( Formula; con; var; _∈̇_; _∧̇_ )
import OrdinaryProfile
import FOL.Semantics
import CodedVocabulary
import K6.Separation
import O7.Definability

module O7.PlugSeparation {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

open OrdinaryProfile 𝒮 using ( Separation; Collection )
open CodedVocabulary 𝒮 using ( isKPairΔ )

private module SemG = FOL.Semantics (hPropAlgebra ℓ) 𝒮
module SatG = SemG.At S id
open SatG using () renaming ( _⊨_ to _⊨ᴳ_ )

module Sep = K6.Separation 𝒮
module O7C = O7.Definability 𝒮

module Plug
  (entry       : S → S → S)
  (Child       : S → S → Type ℓ)
  (child-entry : (x b n : S) → ⟨ entry x b ∈ˢ n ⟩ → Child x n)
  (carrierᶠ    : S)
  (IsNm        : S → Ω)
  (child-name  : (n : S) → ⟨ IsNm n ⟩ → (x : S) → Child x n → ⟨ IsNm x ⟩)
  where

  module N = Sep.Names entry Child child-entry carrierᶠ IsNm child-name
  open N using ( Nm )

  module PlugAtG
    (Cond        : Type ℓ)
    (cnd         : Cond → S)
    (cnd-carrier : (r : Cond) → ⟨ cnd r ∈ˢ carrierᶠ ⟩)
    (G∈          : Cond → Ω)
    (_≈[G]_ _∈[G]_ : S → S → Ω)
    (‖Active‖    : S → S → Ω)
    (≈-sym       : {m n : S} → ⟨ m ≈[G] n ⟩ → ⟨ n ≈[G] m ⟩)
    (∈-congˡ     : {m m' n : S} → ⟨ m ≈[G] m' ⟩ → ⟨ m ∈[G] n ⟩ → ⟨ m' ∈[G] n ⟩)
    (∈-unfold    : (m n : S) → (m ∈[G] n) ≡ ⋁ S (λ y → ‖Active‖ y n ⊓ (m ≈[G] y)))
    (active-value : {x n : S} → ⟨ ‖Active‖ x n ⟩ → ⟨ x ∈[G] n ⟩)
    (active-out  : (x n : S) → ⟨ ‖Active‖ x n ⟩
                 → ⟨ ⋁ Cond (λ r → G∈ r ⊓ (entry x (cnd r) ∈ˢ n)) ⟩)
    (active-in   : (x n : S) (r : Cond) → ⟨ G∈ r ⟩ → ⟨ entry x (cnd r) ∈ˢ n ⟩
                 → ⟨ ‖Active‖ x n ⟩)
    where

    module A = N.AtG Cond cnd cnd-carrier G∈ _≈[G]_ _∈[G]_ ‖Active‖
                     ≈-sym ∈-congˡ ∈-unfold active-value active-out active-in
    open A using ( Agree; _⊨_ )

    module PlugCut
      (sat-cong : ∀ {k} (φ : Formula Nm k) (ν μ : Vec Nm k) → Agree ν μ
                → (ν ⊨ φ) ≡ (μ ⊨ φ))
      (sepᴳ  : Separation)
      (collᴳ : Collection)
      (dom     : S → S)
      (dom-in  : (n : S) → ⟨ IsNm n ⟩ → (x : S) → Child x n → ⟨ x ∈ˢ dom n ⟩)
      (dom-out : (n x : S) → ⟨ x ∈ˢ dom n ⟩ → Child x n)
      (entryBound : Collection → Separation → (D : S) → S)
      (entryBound-in : (coll : Collection) (sep : Separation) (D x p : S)
                     → ⟨ x ∈ˢ D ⟩ → ⟨ p ∈ˢ carrierᶠ ⟩
                     → ⟨ entry x p ∈ˢ entryBound coll sep D ⟩)
      (mk : Separation → (bound : S) → Formula S 1 → S)
      (mk-in : (sep : Separation) (bound : S) (θ : Formula S 1) (e : S)
             → ⟨ e ∈ˢ bound ⟩ → ⟨ (e ∷ []) ⊨ᴳ θ ⟩ → ⟨ e ∈ˢ mk sep bound θ ⟩)
      (mk-sat : (sep : Separation) (bound : S) (θ : Formula S 1) (e : S)
              → ⟨ e ∈ˢ mk sep bound θ ⟩ → ⟨ (e ∷ []) ⊨ᴳ θ ⟩)
      (cut-name : (coll : Collection) (sep : Separation) (D : S) (θ : Formula S 1)
                → ((x : S) → ⟨ x ∈ˢ D ⟩ → ⟨ IsNm x ⟩)
                → ⟨ IsNm (mk sep (entryBound coll sep D) θ) ⟩)
      (forces   : ∀ {k} → Cond → Formula Nm k → Vec Nm k → Ω)
      (truth-at : ∀ {k} (φ : Formula Nm k) (ν : Vec Nm k)
                → (ν ⊨ φ) ≡ ⋁ Cond (λ r → G∈ r ⊓ forces r φ ν))
      -- The two kernel facts Track F does not carry and a supplier must.
      (entry-isKPair : (x b : S) → ⟨ isKPairΔ (entry x b) x b ⟩)
      (kpair-unique  : (q x b : S) → ⟨ isKPairΔ q x b ⟩ → q ≡ entry x b)
      (entry-inj     : {x b y c : S} → entry x b ≡ entry y c → (x ≡ y) × (b ≡ c))
      -- O7 ITSELF, and nothing else.
      (forcesΔ         : ∀ {k} → Formula Nm k → Formula S (suc k))
      (forcesΔ-reading : ∀ {k} (φ : Formula Nm k) (ν : Vec Nm k) (r : Cond)
                       → ((cnd r ∷ O7C.Names.codesOf IsNm ν) ⊨ᴳ forcesΔ φ)
                       ≡ forces r φ ν)
      where

      private
        module D = O7C.Names.Kernel.Datum IsNm entry entry-isKPair kpair-unique
                     entry-inj Cond cnd forces forcesΔ forcesΔ-reading

      -- THE APPLICATION. Every earlier argument is Track F's own; the last two
      -- are O7's output. Agda checks the fit.

      module Cut = A.Cut sat-cong sepᴳ collᴳ dom dom-in dom-out
                         entryBound entryBound-in mk mk-in mk-sat cut-name
                         forces truth-at
                         D.sepΔ D.sepΔ-reading

      -- Track F's Separation field, now standing on O7 alone.

      hasSeparationᴱ : A.OP.Separation
      hasSeparationᴱ = Cut.hasSeparation

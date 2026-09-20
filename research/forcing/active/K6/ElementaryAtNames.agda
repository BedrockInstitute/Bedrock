{-# OPTIONS --cubical --safe --guardedness #-}

-- K6 Track B, seam probe, Track A half. K6/ElementaryAtStructures.agda leaves
-- Track A's five exports as parameters; this file fills them from the real
-- K6.NameBuild and K6.NameValid and re-asks for the two fields.
--
-- The composition is not free of content: Track A's `entryBound` and `mk` take
-- the ground axioms as explicit ARGUMENTS (K6/NameBuild.agda:294, :348,
-- following NameSpace.agda:47-52), while Track B takes them already applied,
-- so the seam is a partial application and the ledger row it produces is
-- exact: Track B's two names cost ground Collection and ground Separation
-- through Track A, ground Union through ⋃ᴳ and ground Pairing through pairOf,
-- and nothing else. Ground PowerSet is NOT spent: `nameBound` reaches this
-- file only as Track A's own parameter and no declaration here applies it.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import Valuation
import OrdinaryProfile
import CodedVocabulary
import K5.Structures
import K6.Elementary
import K6.NameBuild
import K6.NameValid
import Cubical.HITs.PropositionalTruncation as PT

module K6.ElementaryAtNames {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ)) where

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
open import OrdinaryProfile 𝒮 using ( Separation ; Collection ; PowerSet )

module Compose
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
  -- K6/NameBuild.agda:73-93, the part of Track A's Calculus telescope that
  -- K6/ElementaryAtStructures.agda does not already carry.
  (ext-path      : {a b : S} → ((x : S) → (x ∈ˢ a) ≡ (x ∈ˢ b)) → a ≡ b)
  (colAt         : ∀ {k} → Formula S (suc (suc k)) → Vec S k → Formula S 2)
  (colAt-reading : ∀ {k} (φ : Formula S (suc (suc k))) (ps : Vec S k) (y x : S)
                 → ((y ∷ x ∷ []) ⊨ colAt φ ps) ≡ ((y ∷ x ∷ ps) ⊨ φ))
  (separateOf      : Separation → (a : S) → Formula S 1 → S)
  (separateOf-spec : (sep : Separation) (a : S) (φ : Formula S 1) (x : S)
                   → (x ∈ˢ separateOf sep a φ) ≡ ((x ∈ˢ a) ⊓ ((x ∷ []) ⊨ φ)))
  (graph→image : Collection → Separation → (f : S → S) (a : S)
               → (graph : Formula S 2)
               → ((x : S) → ⟨ x ∈ˢ a ⟩ → ⟨ (f x ∷ x ∷ []) ⊨ graph ⟩)
               → ((x : S) → ⟨ x ∈ˢ a ⟩ → (y : S)
                  → ⟨ (y ∷ x ∷ []) ⊨ graph ⟩ → y ≡ f x)
               → Σ[ T ∈ S ] ((z : S) → (z ∈ˢ T)
                   ≡ ⋁ S (λ x → (x ∈ˢ a) ⊓ (z ≈ˢ f x))))
  (⋃ᴳ-spec : (a x : S) → (x ∈ˢ ⋃ᴳ a) ≡ ⋁ S (λ y → (y ∈ˢ a) ⊓ (x ∈ˢ y)))
  -- K6/NameValid.agda:67-98, likewise.
  (child-weight  : (x n : S) → Child x n → ∥ Σ[ b ∈ S ] ⟨ entry x b ∈ˢ n ⟩ ∥₁)
  (name-introᴾ   : (n : S)
                 → ((e : S) → ⟨ e ∈ˢ n ⟩
                    → ∥ Σ[ x ∈ S ] Σ[ b ∈ S ]
                          ((e ≡ entry x b) × ⟨ b ∈ˢ carrierᶠ ⟩) ∥₁)
                 → ((x : S) → Child x n → ⟨ IsNameᴾ x ⟩)
                 → ⟨ IsNameᴾ n ⟩)
  (support  : S → S)
  (nameBound : PowerSet → (C : S) → S)
  (nameBound-contains : (pow : PowerSet) (C n : S) → ⟨ IsNameᴾ n ⟩
                      → ((x : S) → Child x n → ⟨ x ∈ˢ C ⟩)
                      → ⟨ n ∈ˢ nameBound pow C ⟩)
  (nameAtᶠ       : Formula S 2)
  (name-adequate : (t : S) → ((t ∷ carrierᶠ ∷ []) ⊨ nameAtᶠ) ≡ IsNameᴾ t)
  -- The two ground axioms Track A spends, as arguments and never as a record.
  (coll : Collection)
  (sep  : Separation)
  where

  private
    module KS = K5.Structures.Kernel 𝒮
                  entry Child isPropChild child-entry child-wf ∅ᴺ ∅ᴺ-spec
    module PS = KS.PosetSide carrierᶠ _≼ᶜ_ ≼ᶜ-refl ≼ᶜ-trans inhabitedᶜ
                  IsNameᴾ child-nameᴾ
    module EL = K6.Elementary 𝒮
    module NB = K6.NameBuild.Calculus 𝒮 paths ext-path carrierᶠ entry
                  entry-isKPair kpair-unique colAt colAt-reading
                  separateOf separateOf-spec graph→image ⋃ᴳ ⋃ᴳ-spec
    module NV = K6.NameValid.Valid 𝒮 carrierᶠ entry entry-inj Child
                  child-weight IsNameᴾ name-introᴾ separateOf separateOf-spec
                  paths NB.mk NB.mk-bound NB.entryBound NB.entryBound-out
                  support nameBound nameBound-contains nameAtᶠ name-adequate

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
                   ∈-congˡ ∈-congʳ (NB.entryBound coll sep)
                   (NB.entryBound-spec coll sep) (NB.mk sep) (NB.mk-spec sep)
                   (NV.mk-name sep) pairOf pairOf-spec ⋃ᴳ ⋃ᴳ-in support-bound

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

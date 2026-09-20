{-# OPTIONS --cubical --safe --guardedness #-}

-- K6 Track G's consumer seam, against Track A.
--
-- WHAT IT CHECKS, AND WHY IT IS NOT A FORMALITY. K6/Power.agda takes eleven
-- Track A operations as VARIABLES, so a drift in Track A's landed types would
-- show up only when the coordinator assembles. Each alias below has K6/Power's
-- parameter type written out character for character and Track A's landed
-- export as its body.
--
-- It also discharges, mechanically, the silent O3b import the coordinator
-- named: `graph→image`'s result shape and `imageOn-spec` are identical
-- (NameImage.agda:86-87 against StandardNames.agda:284-285), so a filler that
-- called imageOn would typecheck and would pull in the tier-4 MemberImage.
-- Every filler below is a Track A export and `imageOn`, `MemberImage`,
-- `.image` and `image-spec` all measure 0 in this file and in K6/Power.agda.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
open import FOL.Syntax
open import FOL.Semantics using ( )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ ; ∣_∣₁ )
import OrdinaryProfile
import FOL.Semantics
import CodedVocabulary
import K6.NameBuild
import K6.NameValid

module K6.PowerAtNameBuild
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  where

open import FOL.ZFStructure using ( module hPropStructure )
open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open OrdinaryProfile 𝒮 using ( Separation ; Collection ; PowerSet )
open CodedVocabulary 𝒮 using ( isKPairΔ )

private
  module SemG = FOL.Semantics (hPropAlgebra ℓ) 𝒮

open SemG.At S id using () renaming ( _⊨_ to _⊨ᴳ_ )

module Fill
  (paths         : (x y : S) → (x ≈ˢ y) ≡ ((x ≡ y) , isSetS x y))
  (ext-path      : {a b : S} → ((x : S) → (x ∈ˢ a) ≡ (x ∈ˢ b)) → a ≡ b)
  (carrierᶠ      : S)
  (entry         : S → S → S)
  (entry-isKPair : (x b : S) → ⟨ isKPairΔ (entry x b) x b ⟩)
  (kpair-unique  : (q x b : S) → ⟨ isKPairΔ q x b ⟩ → q ≡ entry x b)
  (entry-inj     : {x b y c : S} → entry x b ≡ entry y c → (x ≡ y) × (b ≡ c))
  (Child         : S → S → Type ℓ)
  (child-weight  : (x n : S) → Child x n → ∥ Σ[ b ∈ S ] ⟨ entry x b ∈ˢ n ⟩ ∥₁)
  (IsNameᴾ       : S → Ω)
  (name-introᴾ   : (n : S)
                 → ((e : S) → ⟨ e ∈ˢ n ⟩
                    → ∥ Σ[ x ∈ S ] Σ[ b ∈ S ]
                          ((e ≡ entry x b) × ⟨ b ∈ˢ carrierᶠ ⟩) ∥₁)
                 → ((x : S) → Child x n → ⟨ IsNameᴾ x ⟩)
                 → ⟨ IsNameᴾ n ⟩)
  (colAt         : ∀ {k} → Formula S (suc (suc k)) → Vec S k → Formula S 2)
  (colAt-reading : ∀ {k} (φ : Formula S (suc (suc k))) (ps : Vec S k) (y x : S)
                 → ((y ∷ x ∷ []) ⊨ᴳ colAt φ ps) ≡ ((y ∷ x ∷ ps) ⊨ᴳ φ))
  (separateOf      : Separation → (a : S) → Formula S 1 → S)
  (separateOf-spec : (sep : Separation) (a : S) (φ : Formula S 1) (x : S)
                   → (x ∈ˢ separateOf sep a φ) ≡ ((x ∈ˢ a) ⊓ ((x ∷ []) ⊨ᴳ φ)))
  (graph→image : Collection → Separation → (f : S → S) (a : S)
               → (graph : Formula S 2)
               → ((x : S) → ⟨ x ∈ˢ a ⟩ → ⟨ (f x ∷ x ∷ []) ⊨ᴳ graph ⟩)
               → ((x : S) → ⟨ x ∈ˢ a ⟩ → (y : S)
                  → ⟨ (y ∷ x ∷ []) ⊨ᴳ graph ⟩ → y ≡ f x)
               → Σ[ T ∈ S ] ((z : S) → (z ∈ˢ T)
                   ≡ ⋁ S (λ x → (x ∈ˢ a) ⊓ (z ≈ˢ f x))))
  (⋃ᴳ      : S → S)
  (⋃ᴳ-spec : (a x : S) → (x ∈ˢ ⋃ᴳ a) ≡ ⋁ S (λ y → (y ∈ˢ a) ⊓ (x ∈ˢ y)))
  (support   : S → S)
  (nameBound : PowerSet → (C : S) → S)
  (nameBound-contains : (pow : PowerSet) (C n : S) → ⟨ IsNameᴾ n ⟩
                      → ((x : S) → Child x n → ⟨ x ∈ˢ C ⟩)
                      → ⟨ n ∈ˢ nameBound pow C ⟩)
  (nameAtᶠ       : Formula S 2)
  (name-adequate : (t : S) → ((t ∷ carrierᶠ ∷ []) ⊨ᴳ nameAtᶠ) ≡ IsNameᴾ t)
  where

  module A = K6.NameBuild.Calculus 𝒮 paths ext-path carrierᶠ entry
               entry-isKPair kpair-unique colAt colAt-reading
               separateOf separateOf-spec graph→image ⋃ᴳ ⋃ᴳ-spec

  module V = K6.NameValid.Valid 𝒮 carrierᶠ entry entry-inj Child child-weight
               IsNameᴾ name-introᴾ separateOf separateOf-spec paths
               A.mk A.mk-bound A.entryBound A.entryBound-out
               support nameBound nameBound-contains nameAtᶠ name-adequate

  -- The eleven slots of K6/Power.agda's Conditional telescope that Track A
  -- owns. Each type below is pasted from K6/Power.agda and each body is
  -- Track A's export. Nothing here calls an image route.

  mk : Separation → (bound : S) → Formula S 1 → S
  mk = A.mk

  mk-in : (sep' : Separation) (bound : S) (θ : Formula S 1) (e : S)
        → ⟨ e ∈ˢ bound ⟩ → ⟨ (e ∷ []) ⊨ᴳ θ ⟩ → ⟨ e ∈ˢ mk sep' bound θ ⟩
  mk-in = A.mk-in

  mk-bound : (sep' : Separation) (bound : S) (θ : Formula S 1) (e : S)
           → ⟨ e ∈ˢ mk sep' bound θ ⟩ → ⟨ e ∈ˢ bound ⟩
  mk-bound = A.mk-bound

  mk-sat : (sep' : Separation) (bound : S) (θ : Formula S 1) (e : S)
         → ⟨ e ∈ˢ mk sep' bound θ ⟩ → ⟨ (e ∷ []) ⊨ᴳ θ ⟩
  mk-sat = A.mk-sat

  entryBound : Collection → Separation → (D : S) → S
  entryBound = A.entryBound

  entryBound-in : (coll' : Collection) (sep' : Separation) (D x p : S)
                → ⟨ x ∈ˢ D ⟩ → ⟨ p ∈ˢ carrierᶠ ⟩
                → ⟨ entry x p ∈ˢ entryBound coll' sep' D ⟩
  entryBound-in = A.entryBound-in

  entryBound-out : (coll' : Collection) (sep' : Separation) (D e : S)
                 → ⟨ e ∈ˢ entryBound coll' sep' D ⟩
                 → ⟨ ⋁ S (λ x → (x ∈ˢ D) ⊓
                       ⋁ S (λ p → (p ∈ˢ carrierᶠ) ⊓ (e ≈ˢ entry x p))) ⟩
  entryBound-out = A.entryBound-out

  cut-name : (coll' : Collection) (sep' : Separation) (D : S)
             (θ : Formula S 1)
           → ((x : S) → ⟨ x ∈ˢ D ⟩ → ⟨ IsNameᴾ x ⟩)
           → ⟨ IsNameᴾ (mk sep' (entryBound coll' sep' D) θ) ⟩
  cut-name = V.cut-name

  candidates : Separation → PowerSet → (σ : S) → S
  candidates = V.candidates

  candidates-name : (sep' : Separation) (pow' : PowerSet) (σ χ : S)
                  → ⟨ χ ∈ˢ candidates sep' pow' σ ⟩ → ⟨ IsNameᴾ χ ⟩
  candidates-name = V.candidates-name

  candidates-contains : (sep' : Separation) (pow' : PowerSet) (σ χ : S)
                      → ⟨ IsNameᴾ χ ⟩
                      → ((x : S) → Child x χ → ⟨ x ∈ˢ support σ ⟩)
                      → ⟨ χ ∈ˢ candidates sep' pow' σ ⟩
  candidates-contains = V.candidates-contains

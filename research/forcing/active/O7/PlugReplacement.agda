{-# OPTIONS --cubical --safe --guardedness #-}

-- O7, THE AIRTIGHT DISCHARGE AT TRACK H (Collection).
--
-- Same method as O7/PlugSeparation.agda: the whole of K6.Replacement's module
-- Collected except colΔ and colΔ-reading is taken as a telescope, the real
-- module is applied, and O7's colΔ goes into the two slots K6 declared.
--
-- ONE PARAMETER HERE THAT TRACK H DOES NOT CARRY, beyond the datum itself:
-- cnd-cndOf. Track H carries cndOf-cnd (K6/Replacement.agda:250), which runs
-- the other way. The datum reads at the code cnd r of a Cond, and Track H's
-- field reads at a bare code q together with its membership, so the supplier
-- needs cnd (cndOf q hq) ≡ q. K6/Replacement.agda:128-130 records that at the
-- instance Cond is a plain Σ, cndOf q hq is (q , hq) and this is refl.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
open import FOL.Syntax using ( Formula; con; var; _∈̇_ )
import OrdinaryProfile
import FOL.Semantics
import CodedVocabulary
import K6.Replacement
import O7.Definability

module O7.PlugReplacement {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

open OrdinaryProfile 𝒮 using ( Separation; Collection )
open CodedVocabulary 𝒮 using ( isKPairΔ )

private module SemG = FOL.Semantics (hPropAlgebra ℓ) 𝒮
module SatG = SemG.At S id
open SatG using () renaming ( _⊨_ to _⊨ᴳ_ )

module Rep = K6.Replacement 𝒮
module O7C = O7.Definability 𝒮

module Plug
  (entry       : S → S → S)
  (Child       : S → S → Type ℓ)
  (child-entry : (x b n : S) → ⟨ entry x b ∈ˢ n ⟩ → Child x n)
  (carrierᶠ    : S)
  (IsNm        : S → Ω)
  (child-name  : (n : S) → ⟨ IsNm n ⟩ → (x : S) → Child x n → ⟨ IsNm x ⟩)
  where

  module N = Rep.Names entry Child child-entry carrierᶠ IsNm child-name
  open N using ( Nm )

  module PlugAtG
    (Cond        : Type ℓ)
    (cnd         : Cond → S)
    (cnd-carrier : (r : Cond) → ⟨ cnd r ∈ˢ carrierᶠ ⟩)
    (cndOf       : (q : S) → ⟨ q ∈ˢ carrierᶠ ⟩ → Cond)
    (cndOf-cnd   : (r : Cond) → cndOf (cnd r) (cnd-carrier r) ≡ r)
    (G∈          : Cond → Ω)
    (_≈[G]_ _∈[G]_ : S → S → Ω)
    (‖Active‖    : S → S → Ω)
    (≈-refl      : (x : S) → ⟨ x ≈[G] x ⟩)
    (∈-unfold    : (m n : S) → (m ∈[G] n) ≡ ⋁ S (λ y → ‖Active‖ y n ⊓ (m ≈[G] y)))
    (active-value : {x n : S} → ⟨ ‖Active‖ x n ⟩ → ⟨ x ∈[G] n ⟩)
    (active-out  : (x n : S) → ⟨ ‖Active‖ x n ⟩
                 → ⟨ ⋁ Cond (λ r → G∈ r ⊓ (entry x (cnd r) ∈ˢ n)) ⟩)
    (active-in   : (x n : S) (r : Cond) → ⟨ G∈ r ⟩ → ⟨ entry x (cnd r) ∈ˢ n ⟩
                 → ⟨ ‖Active‖ x n ⟩)
    where

    module A = N.AtG Cond cnd cnd-carrier cndOf cndOf-cnd G∈ _≈[G]_ _∈[G]_
                     ‖Active‖ ≈-refl ∈-unfold active-value active-out active-in
    open A using ( Agree; _⊨_ )

    module PlugCollected
      (sat-cong : ∀ {k} (ψ : Formula Nm k) (ν μ : Vec Nm k) → Agree ν μ
                → (ν ⊨ ψ) ≡ (μ ⊨ ψ))
      (sepᴳ  : Separation)
      (collᴳ : Collection)
      (dom     : S → S)
      (dom-in  : (n x p : S) → ⟨ entry x p ∈ˢ n ⟩ → ⟨ x ∈ˢ dom n ⟩)
      (dom-out : (n x : S) → ⟨ x ∈ˢ dom n ⟩ → ⟨ ⋁ S (λ p → entry x p ∈ˢ n) ⟩)
      (⋃ᴳ    : S → S)
      (⋃ᴳ-in : (b y x : S) → ⟨ y ∈ˢ b ⟩ → ⟨ x ∈ˢ y ⟩ → ⟨ x ∈ˢ ⋃ᴳ b ⟩)
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
      (nameFo : Formula S 1)
      (nameFo-reading : (t : S) → ((t ∷ []) ⊨ᴳ nameFo) ≡ IsNm t)
      (colAt : ∀ {k} → Formula S (suc (suc k)) → Vec S k → Formula S 2)
      (colAt-reading : ∀ {k} (ψ : Formula S (suc (suc k))) (ps : Vec S k) (y x : S)
                     → ((y ∷ x ∷ []) ⊨ᴳ colAt ψ ps) ≡ ((y ∷ x ∷ ps) ⊨ᴳ ψ))
      (forces   : ∀ {k} → Cond → Formula Nm k → Vec Nm k → Ω)
      (truth-at : ∀ {k} (ψ : Formula Nm k) (ν : Vec Nm k)
                → (ν ⊨ ψ) ≡ ⋁ Cond (λ r → G∈ r ⊓ forces r ψ ν))
      (lem : LEM ℓ)
      -- The kernel facts and the one direction of cndOf a supplier must carry.
      (entry-isKPair : (x b : S) → ⟨ isKPairΔ (entry x b) x b ⟩)
      (kpair-unique  : (q x b : S) → ⟨ isKPairΔ q x b ⟩ → q ≡ entry x b)
      (entry-inj     : {x b y c : S} → entry x b ≡ entry y c → (x ≡ y) × (b ≡ c))
      (cnd-cndOf     : (q : S) (hq : ⟨ q ∈ˢ carrierᶠ ⟩) → cnd (cndOf q hq) ≡ q)
      -- O7 ITSELF, and nothing else.
      (forcesΔ         : ∀ {k} → Formula Nm k → Formula S (suc k))
      (forcesΔ-reading : ∀ {k} (φ : Formula Nm k) (ν : Vec Nm k) (r : Cond)
                       → ((cnd r ∷ O7C.Names.codesOf IsNm ν) ⊨ᴳ forcesΔ φ)
                       ≡ forces r φ ν)
      where

      private
        module D = O7C.Names.Kernel.Replacement IsNm entry entry-isKPair
                     kpair-unique entry-inj Cond cnd carrierᶠ cndOf cnd-cndOf
                     forces forcesΔ forcesΔ-reading

      module Collected = A.Collected sat-cong sepᴳ collᴳ dom dom-in dom-out
                           ⋃ᴳ ⋃ᴳ-in entryBound entryBound-in mk mk-in mk-sat
                           cut-name nameFo nameFo-reading colAt colAt-reading
                           forces truth-at
                           D.colΔ D.colΔ-reading
                           lem

      hasReplacementᴱ : A.OP.Collection
      hasReplacementᴱ = Collected.hasReplacement

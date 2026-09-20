{-# OPTIONS --cubical --safe --guardedness #-}

-- O7, THE AIRTIGHT DISCHARGE AT TRACK E (PowerSet).
--
-- Same method as the other two plugs. The whole of K6.Power's module
-- Conditional except powΔ and powΔ-reading is taken as a telescope, the real
-- module is applied, and O7's powΔ goes into the two slots K6 declared.
--
-- Track E states Cond as the Σ type itself and reads the condition code as
-- `fst r`, where Tracks F and H carry an abstract Cond with cnd. The datum is
-- the SAME datum: the wrapper O7.Definability's module Power instantiates
-- (Cond , cnd) at (Σ[ p ∈ S ] ⟨ p ∈ˢ carrierᶠ ⟩ , fst).

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
open import FOL.Syntax using ( Formula; con; var; _∈̇_ )
import OrdinaryProfile
import FOL.Semantics
import CodedVocabulary
import Cubical.HITs.PropositionalTruncation as PT
import K6.Power
import O7.Definability

open PT using ( ∥_∥₁ )

module O7.PlugPower {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

open OrdinaryProfile 𝒮 using ( Separation; Collection; PowerSet )
open CodedVocabulary 𝒮 using ( isKPairΔ )

private module SemG = FOL.Semantics (hPropAlgebra ℓ) 𝒮
module SatG = SemG.At S id
open SatG using () renaming ( _⊨_ to _⊨ᴳ_ )

module Pow = K6.Power 𝒮
module O7C = O7.Definability 𝒮

module Plug
  (entry       : S → S → S)
  (entry-inj   : {x b y c : S} → entry x b ≡ entry y c → (x ≡ y) × (b ≡ c))
  (Child       : S → S → Type ℓ)
  (child-weight : (x n : S) → Child x n → ∥ Σ[ b ∈ S ] ⟨ entry x b ∈ˢ n ⟩ ∥₁)
  (carrierᶠ    : S)
  (IsNameᴾ     : S → Ω)
  (child-nameᴾ : (n : S) → ⟨ IsNameᴾ n ⟩ → (x : S) → Child x n → ⟨ IsNameᴾ x ⟩)
  (paths       : (x y : S) → (x ≈ˢ y) ≡ ((x ≡ y) , isSetS x y))
  where

  module K = Pow.Kernel entry entry-inj Child child-weight carrierᶠ
                        IsNameᴾ child-nameᴾ paths
  open K using ( Cond; Nameᴾ )

  module PlugAt
    (G             : Cond → Ω)
    (_≈[G]_ _∈[G]_ : S → S → Ω)
    where

    module T = K.At G _≈[G]_ _∈[G]_
    open T using ( ‖Active‖; 𝒮ᴾ )

    module PlugLaws
      (≈-sym         : {m n : S} → ⟨ m ≈[G] n ⟩ → ⟨ n ≈[G] m ⟩)
      (≈-trans       : {m n r : S} → ⟨ m ≈[G] n ⟩ → ⟨ n ≈[G] r ⟩ → ⟨ m ≈[G] r ⟩)
      (∈-congˡ       : {m m' n : S} → ⟨ m ≈[G] m' ⟩ → ⟨ m ∈[G] n ⟩ → ⟨ m' ∈[G] n ⟩)
      (value-extensional : (m n : S) → ((r : S) → (r ∈[G] m) ≡ (r ∈[G] n))
                         → ⟨ m ≈[G] n ⟩)
      (∈-unfold      : (m n : S) → (m ∈[G] n)
                     ≡ ⋁ S (λ y → ‖Active‖ y n ⊓ (m ≈[G] y)))
      (active-child  : (x n : S) → ⟨ ‖Active‖ x n ⟩ → Child x n)
      (active-value  : {x n : S} → ⟨ ‖Active‖ x n ⟩ → ⟨ x ∈[G] n ⟩)
      (entry-value   : (n x p : S) (hp : ⟨ p ∈ˢ carrierᶠ ⟩) → ⟨ G (p , hp) ⟩
                     → ⟨ entry x p ∈ˢ n ⟩ → ⟨ x ∈[G] n ⟩)
      where

      module L = T.Laws ≈-sym ≈-trans ∈-congˡ value-extensional ∈-unfold
                        active-child active-value entry-value
      -- K6/Power.agda:271-273 opens this renaming privately, so it is rebuilt
      -- here from the same two definitions and is the same function.
      private module SemP = FOL.Semantics (hPropAlgebra ℓ) 𝒮ᴾ
      open SemP.At Nameᴾ id using () renaming ( _⊨_ to _⊨ᴾ_ )

      module PlugConditional
        (pos : ⟨ ⋁ Cond (λ q → G q) ⟩)
        (sep  : Separation)
        (coll : Collection)
        (pow  : PowerSet)
        (mk         : Separation → (bound : S) → Formula S 1 → S)
        (mk-in      : (sep' : Separation) (bound : S) (θ : Formula S 1) (e : S)
                    → ⟨ e ∈ˢ bound ⟩ → ⟨ (e ∷ []) ⊨ᴳ θ ⟩
                    → ⟨ e ∈ˢ mk sep' bound θ ⟩)
        (mk-bound   : (sep' : Separation) (bound : S) (θ : Formula S 1) (e : S)
                    → ⟨ e ∈ˢ mk sep' bound θ ⟩ → ⟨ e ∈ˢ bound ⟩)
        (mk-sat     : (sep' : Separation) (bound : S) (θ : Formula S 1) (e : S)
                    → ⟨ e ∈ˢ mk sep' bound θ ⟩ → ⟨ (e ∷ []) ⊨ᴳ θ ⟩)
        (entryBound : Collection → Separation → (D : S) → S)
        (entryBound-in : (coll' : Collection) (sep' : Separation) (D x p : S)
                       → ⟨ x ∈ˢ D ⟩ → ⟨ p ∈ˢ carrierᶠ ⟩
                       → ⟨ entry x p ∈ˢ entryBound coll' sep' D ⟩)
        (entryBound-out : (coll' : Collection) (sep' : Separation) (D e : S)
                        → ⟨ e ∈ˢ entryBound coll' sep' D ⟩
                        → ⟨ ⋁ S (λ x → (x ∈ˢ D) ⊓
                              ⋁ S (λ p → (p ∈ˢ carrierᶠ) ⊓ (e ≈ˢ entry x p))) ⟩)
        (cut-name   : (coll' : Collection) (sep' : Separation) (D : S)
                      (θ : Formula S 1)
                    → ((x : S) → ⟨ x ∈ˢ D ⟩ → ⟨ IsNameᴾ x ⟩)
                    → ⟨ IsNameᴾ (mk sep' (entryBound coll' sep' D) θ) ⟩)
        (support    : S → S)
        (candidates : Separation → PowerSet → (σ : S) → S)
        (candidates-name : (sep' : Separation) (pow' : PowerSet) (σ χ : S)
                         → ⟨ χ ∈ˢ candidates sep' pow' σ ⟩ → ⟨ IsNameᴾ χ ⟩)
        (candidates-contains : (sep' : Separation) (pow' : PowerSet) (σ χ : S)
                             → ⟨ IsNameᴾ χ ⟩
                             → ((x : S) → Child x χ → ⟨ x ∈ˢ support σ ⟩)
                             → ⟨ χ ∈ˢ candidates sep' pow' σ ⟩)
        (support-in    : (n : S) → ⟨ IsNameᴾ n ⟩ → (x : S) → Child x n
                       → ⟨ x ∈ˢ support n ⟩)
        (support-valid : (n : S) → ⟨ IsNameᴾ n ⟩ → (x : S)
                       → ⟨ x ∈ˢ support n ⟩ → ⟨ IsNameᴾ x ⟩)
        (forces   : ∀ {k} → Cond → Formula Nameᴾ k → Vec Nameᴾ k → Ω)
        (truth-at : ∀ {k} (φ : Formula Nameᴾ k) (ν : Vec Nameᴾ k)
                  → (ν ⊨ᴾ φ) ≡ ⋁ Cond (λ p → G p ⊓ forces p φ ν))
        (sepᴾ : OrdinaryProfile.Separation 𝒮ᴾ)
        -- The kernel facts a supplier must carry beyond Track E's own.
        (entry-isKPair : (x b : S) → ⟨ isKPairΔ (entry x b) x b ⟩)
        (kpair-unique  : (q x b : S) → ⟨ isKPairΔ q x b ⟩ → q ≡ entry x b)
        -- O7 ITSELF, and nothing else.
        (forcesΔ         : ∀ {k} → Formula Nameᴾ k → Formula S (suc k))
        (forcesΔ-reading : ∀ {k} (φ : Formula Nameᴾ k) (ν : Vec Nameᴾ k)
                           (r : Cond)
                         → ((fst r ∷ O7C.Names.codesOf IsNameᴾ ν) ⊨ᴳ forcesΔ φ)
                         ≡ forces r φ ν)
        where

        private
          module D = O7C.Names.Kernel.Power IsNameᴾ entry entry-isKPair
                       kpair-unique entry-inj carrierᶠ forces forcesΔ
                       forcesΔ-reading

        module Cond' = L.Conditional pos sep coll pow
                         mk mk-in mk-bound mk-sat
                         entryBound entryBound-in entryBound-out cut-name
                         support candidates candidates-name candidates-contains
                         support-in support-valid
                         forces truth-at
                         D.powΔ D.powΔ-reading
                         sepᴾ

        hasPowerᴱ : OrdinaryProfile.PowerSet 𝒮ᴾ
        hasPowerᴱ = Cond'.hasPower

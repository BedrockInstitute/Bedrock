{-# OPTIONS --cubical --safe --guardedness #-}


open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
open import FOL.Syntax
open import FOL.Manipulation.ConstantMapping using ( embed )
open import Cubical.Data.Vec using ( _++_ )
open import Cubical.Induction.WellFounded using ( WellFounded )
open import Cubical.HITs.PropositionalTruncation using ( ∥_∥₁ )
import OrdinaryProfile
import Valuation
import K4.Algebra
import K4.Implication
import K5.Frame
import K5.Structures
import K5.ExtensionSat
import K6.Definability
import K6.TruthSeam

import K6.ForcesTruth
module K6.ProbeE5
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
         → (ZFStructure._≈ˢ_ 𝒮 x y) ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  (sep : OrdinaryProfile.Separation 𝒮)
  (carrier order : ZFStructure.S 𝒮)
  (B : ZFStructure.S 𝒮)
  (L : K4.Algebra.Lattice 𝒮 B)
  (Cm : K4.Algebra.Complement 𝒮 B L)
  (Kc : K4.Algebra.CodedComplete 𝒮 B L)
  (fb : K5.Frame.Poset.ForcingBase 𝒮 carrier order B L Cm)
  (IsNameᴾ IsNameᴮ : ZFStructure.S 𝒮 → hProp ℓ)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open K4.Algebra 𝒮 using ( Pt ; _≤ᴮ_ )
open K4.Implication 𝒮 ext paths B L Cm using ( _⊓ᴮ_ ; _⊔ᴮ_ ; _⇒ᴮ_ ; ⊥ᴮ )
open Valuation 𝒮 using ( Conditions )

module FP = K5.Frame.Poset 𝒮 carrier order
module FT = K6.ForcesTruth 𝒮 ext paths sep carrier order B L Cm Kc fb IsNameᴾ IsNameᴮ

Src : ℕ → Type ℓ
Src k = Formula (⊥* {ℓ}) k

module Kernel
  (entry       : S → S → S)
  (Child       : S → S → Type ℓ)
  (isPropChild : (x n : S) → isProp (Child x n))
  (child-entry : (x b n : S) → ⟨ entry x b ∈ˢ n ⟩ → Child x n)
  (child-wf    : WellFounded Child)
  (∅ᴺ          : S)
  (∅ᴺ-spec     : (z : S) → (z ∈ˢ ∅ᴺ) ≡ ⊥)
  (_≼ᶜ_        : Conditions carrier → Conditions carrier → Ω)
  (≼ᶜ-refl     : (p : Conditions carrier) → ⟨ p ≼ᶜ p ⟩)
  (≼ᶜ-trans    : {p q r : Conditions carrier} → ⟨ p ≼ᶜ q ⟩ → ⟨ q ≼ᶜ r ⟩ → ⟨ p ≼ᶜ r ⟩)
  (inhabitedᶜ  : ∥ Conditions carrier ∥₁)
  (child-nameᴾ : (n : S) → ⟨ IsNameᴾ n ⟩ → (x : S) → Child x n → ⟨ IsNameᴾ x ⟩)
  (child-nameᴮ : (n : S) → ⟨ IsNameᴮ n ⟩ → (x : S) → Child x n → ⟨ IsNameᴮ x ⟩)
  where

  module FK = FT.Kernel entry Child isPropChild child-entry child-wf ∅ᴺ ∅ᴺ-spec _≼ᶜ_ ≼ᶜ-refl ≼ᶜ-trans inhabitedᶜ child-nameᴾ child-nameᴮ

  module At (G : FK.PS.P.Sub) where

    module FA = FK.At G

    module Engine
      (fil : FT.TSM.TAF.GI.FS.isFilter G)
      (meets : FT.TSM.TAF.C.MeetsAll G)
      (cob : FT.TSM.TAF.C.CodeOfBelow)
      (boc : FT.TSM.TAF.C.BelowOfCode)
      (eqᴬ memᴬ : S → S → Pt B)
      (val : ∀ {k} → Src k → Vec FT.TSM.Nameᴮ k → Pt B)
      (law-∈ : ∀ {k} (a b : Fin k) (ν : Vec FT.TSM.Nameᴮ k)
             → val (var a ∈̇ var b) ν ≡ memᴬ (fst (lookup a ν)) (fst (lookup b ν)))
      (law-≐ : ∀ {k} (a b : Fin k) (ν : Vec FT.TSM.Nameᴮ k)
             → val (var a ≐ var b) ν ≡ eqᴬ (fst (lookup a ν)) (fst (lookup b ν)))
      (law-∧ : ∀ {k} (φ ψ : Src k) (ν : Vec FT.TSM.Nameᴮ k)
             → val (φ ∧̇ ψ) ν ≡ (val φ ν ⊓ᴮ val ψ ν))
      (law-∨ : ∀ {k} (φ ψ : Src k) (ν : Vec FT.TSM.Nameᴮ k)
             → val (φ ∨̇ ψ) ν ≡ (val φ ν ⊔ᴮ val ψ ν))
      (law-⇒ : ∀ {k} (φ ψ : Src k) (ν : Vec FT.TSM.Nameᴮ k)
             → val (φ ⇒̇ ψ) ν ≡ (val φ ν ⇒ᴮ val ψ ν))
      (law-⊥ : ∀ {k} (ν : Vec FT.TSM.Nameᴮ k) → val {k} ⊥̇ ν ≡ ⊥ᴮ)
      (law-∃-ub   : ∀ {k} (φ : Src (suc k)) (ν : Vec FT.TSM.Nameᴮ k) (σ : FT.TSM.Nameᴮ)
                  → ⟨ val φ (σ ∷ ν) ≤ᴮ val (∃̇ φ) ν ⟩)
      (law-∃-lub  : ∀ {k} (φ : Src (suc k)) (ν : Vec FT.TSM.Nameᴮ k) (c : Pt B)
                  → ((σ : FT.TSM.Nameᴮ) → ⟨ val φ (σ ∷ ν) ≤ᴮ c ⟩)
                  → ⟨ val (∃̇ φ) ν ≤ᴮ c ⟩)
      (law-∀-lb   : ∀ {k} (φ : Src (suc k)) (ν : Vec FT.TSM.Nameᴮ k) (σ : FT.TSM.Nameᴮ)
                  → ⟨ val (∀̇ φ) ν ≤ᴮ val φ (σ ∷ ν) ⟩)
      (law-∀-glb  : ∀ {k} (φ : Src (suc k)) (ν : Vec FT.TSM.Nameᴮ k) (c : Pt B)
                  → ((σ : FT.TSM.Nameᴮ) → ⟨ c ≤ᴮ val φ (σ ∷ ν) ⟩)
                  → ⟨ c ≤ᴮ val (∀̇ φ) ν ⟩)
      (law-∃∈-ub  : ∀ {k} (j : Fin k) (φ : Src (suc k)) (ν : Vec FT.TSM.Nameᴮ k)
                    (σ : FT.TSM.Nameᴮ)
                  → ⟨ (memᴬ (fst σ) (fst (lookup j ν)) ⊓ᴮ val φ (σ ∷ ν))
                      ≤ᴮ val (∃̇∈ (var j) φ) ν ⟩)
      (law-∃∈-lub : ∀ {k} (j : Fin k) (φ : Src (suc k)) (ν : Vec FT.TSM.Nameᴮ k)
                    (c : Pt B)
                  → ((σ : FT.TSM.Nameᴮ)
                     → ⟨ (memᴬ (fst σ) (fst (lookup j ν)) ⊓ᴮ val φ (σ ∷ ν)) ≤ᴮ c ⟩)
                  → ⟨ val (∃̇∈ (var j) φ) ν ≤ᴮ c ⟩)
      (law-∀∈-lb  : ∀ {k} (j : Fin k) (φ : Src (suc k)) (ν : Vec FT.TSM.Nameᴮ k)
                    (σ : FT.TSM.Nameᴮ)
                  → ⟨ val (∀̇∈ (var j) φ) ν
                      ≤ᴮ (memᴬ (fst σ) (fst (lookup j ν)) ⇒ᴮ val φ (σ ∷ ν)) ⟩)
      (law-∀∈-glb : ∀ {k} (j : Fin k) (φ : Src (suc k)) (ν : Vec FT.TSM.Nameᴮ k)
                    (c : Pt B)
                  → ((σ : FT.TSM.Nameᴮ) → ⟨ c ≤ᴮ (memᴬ (fst σ) (fst (lookup j ν))
                                              ⇒ᴮ val φ (σ ∷ ν)) ⟩)
                  → ⟨ c ≤ᴮ val (∀̇∈ (var j) φ) ν ⟩)
      -- O1, and the two of them are the whole of it.
      (atom-∈ : (σ τ : FT.TSM.Nameᴮ) → FA.TA._∈ᵁ_ σ τ ≡ FT.TSM.TAF.GI.Uof G (memᴬ (fst σ) (fst τ)))
      (atom-≐ : (σ τ : FT.TSM.Nameᴮ) → FA.TA._≈ᵁ_ σ τ ≡ FT.TSM.TAF.GI.Uof G (eqᴬ (fst σ) (fst τ)))
      where

      module FE = FA.Engine fil meets cob boc eqᴬ memᴬ val law-∈ law-≐ law-∧ law-∨ law-⇒ law-⊥ law-∃-ub law-∃-lub law-∀-lb law-∀-glb law-∃∈-ub law-∃∈-lub law-∀∈-lb law-∀∈-glb atom-∈ atom-≐

      module Conditional
        (trᴮ         : S → S)
        (trᴮ-name    : (n : S) → ⟨ IsNameᴾ n ⟩ → ⟨ IsNameᴮ (trᴮ n) ⟩)
        (≈-agree     : (m n : S) → FA.EA._≈[G]_ m n ≡ FA.EA._≈[U]_ (trᴮ m) (trᴮ n))
        (∈-agree     : (m n : S) → FA.EA._∈[G]_ m n ≡ FA.EA._∈[U]_ (trᴮ m) (trᴮ n))
        (ext-surjective : (n : S) → ⟨ IsNameᴮ n ⟩
                        → Σ[ τ ∈ (Σ[ m ∈ S ] ⟨ IsNameᴾ m ⟩) ]
                            ⟨ FA.EA._≈[U]_ (trᴮ (fst τ)) n ⟩)
        (supply : ∀ {k} (φ : Formula FA.Nameᴾ k) → FE.Supply (FA.D.srcOf φ))
        (lem : LEM ℓ)
        where

        module FC = FE.Conditional trᴮ trᴮ-name ≈-agree ∈-agree ext-surjective supply lem

        check : ∀ {k} (φ : Formula FA.Nameᴾ k) (ν : Vec FA.Nameᴾ k)
              → (ν FA.D.⊨ φ) ≡ ⋁ FP.Cond (λ p → (FA.G∈ p) ⊓ FC.forces p φ ν)
        check = FC.truth-at

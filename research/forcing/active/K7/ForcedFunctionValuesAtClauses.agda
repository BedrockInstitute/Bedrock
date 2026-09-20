{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile
import K4.Algebra
import K4.Implication
import K5.Clauses
import K7.ForcedFunctionValues

module K7.ForcedFunctionValuesAtClauses
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
         → (ZFStructure._≈ˢ_ 𝒮 x y) ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  (B : ZFStructure.S 𝒮)
  (L : K4.Algebra.Lattice 𝒮 B)
  (Cm : K4.Algebra.Complement 𝒮 B L)
  (carrierᶠ : ZFStructure.S 𝒮)
  (_≼ᶜ_ : ZFStructure.S 𝒮 → ZFStructure.S 𝒮 → hProp ℓ)
  (IsNameᴮ : ZFStructure.S 𝒮 → hProp ℓ)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( var; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ⊥̇; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.Data.Empty as Empty

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open K4.Algebra 𝒮 using ( Pt; _≤ᴮ_ )
open K4.Implication 𝒮 ext paths B L Cm using ( ⊥ᴮ; _⊓ᴮ_; _⊔ᴮ_; _⇒ᴮ_ )

module CL = K5.Clauses 𝒮 ext paths B L Cm carrierᶠ _≼ᶜ_ IsNameᴮ
open CL using ( Cond; Nameᴮ; Envᴮ; Src; DenseBelow )

module Core
  (iᶠ        : Cond → Pt B)
  (_⊩ᴮ_      : Cond → Pt B → Ω)
  (⊩ᴮ-spec   : (p : Cond) (b : Pt B) → (p ⊩ᴮ b) ≡ (iᶠ p ≤ᴮ b))
  (≼-refl    : (p : S) → ⟨ p ∈ˢ carrierᶠ ⟩ → ⟨ p ≼ᶜ p ⟩)
  (≼-trans   : (r q p : S) → ⟨ r ∈ˢ carrierᶠ ⟩ → ⟨ q ∈ˢ carrierᶠ ⟩
             → ⟨ p ∈ˢ carrierᶠ ⟩
             → ⟨ r ≼ᶜ q ⟩ → ⟨ q ≼ᶜ p ⟩ → ⟨ r ≼ᶜ p ⟩)
  (⊩ᴮ-mono   : (p q : Cond) (b : Pt B)
             → ⟨ (fst q) ≼ᶜ (fst p) ⟩ → ⟨ p ⊩ᴮ b ⟩ → ⟨ q ⊩ᴮ b ⟩)
  (⊩ᴮ-down   : (p : Cond) (b : Pt B)
             → ⟨ p ⊩ᴮ b ⟩ → ⟨ DenseBelow p (λ r → r ⊩ᴮ b) ⟩)
  (⊩ᴮ-reg    : (p : Cond) (b : Pt B)
             → ⟨ DenseBelow p (λ r → r ⊩ᴮ b) ⟩ → ⟨ p ⊩ᴮ b ⟩)
  (⊩ᴮ-⊥      : (p : Cond) → ⟨ p ⊩ᴮ ⊥ᴮ ⟩ → ⟨ ⊥ ⟩)
  (⊩ᴮ-extend : (q : Cond) (b : Pt B) → (((iᶠ q ⊓ᴮ b) ≡ ⊥ᴮ) → ⟨ ⊥ ⟩)
             → ⟨ ⋁ Cond (λ r → ((fst r) ≼ᶜ (fst q)) ⊓ (r ⊩ᴮ b)) ⟩)
  (eqᴬ memᴬ  : S → S → Pt B)
  (val       : ∀ {k} → Src k → Envᴮ k → Pt B)
  (law-∈ : ∀ {k} (a b : Fin k) (ν : Envᴮ k)
         → val (var a ∈̇ var b) ν ≡ memᴬ (fst (lookup a ν)) (fst (lookup b ν)))
  (law-≐ : ∀ {k} (a b : Fin k) (ν : Envᴮ k)
         → val (var a ≐ var b) ν ≡ eqᴬ (fst (lookup a ν)) (fst (lookup b ν)))
  (law-∧ : ∀ {k} (φ ψ : Src k) (ν : Envᴮ k)
         → val (φ ∧̇ ψ) ν ≡ (val φ ν ⊓ᴮ val ψ ν))
  (law-∨ : ∀ {k} (φ ψ : Src k) (ν : Envᴮ k)
         → val (φ ∨̇ ψ) ν ≡ (val φ ν ⊔ᴮ val ψ ν))
  (law-⇒ : ∀ {k} (φ ψ : Src k) (ν : Envᴮ k)
         → val (φ ⇒̇ ψ) ν ≡ (val φ ν ⇒ᴮ val ψ ν))
  (law-⊥ : ∀ {k} (ν : Envᴮ k) → val {k} ⊥̇ ν ≡ ⊥ᴮ)
  (law-∃-ub   : ∀ {k} (φ : Src (suc k)) (ν : Envᴮ k) (σ : Nameᴮ)
              → ⟨ val φ (σ ∷ ν) ≤ᴮ val (∃̇ φ) ν ⟩)
  (law-∃-lub  : ∀ {k} (φ : Src (suc k)) (ν : Envᴮ k) (c : Pt B)
              → ((σ : Nameᴮ) → ⟨ val φ (σ ∷ ν) ≤ᴮ c ⟩)
              → ⟨ val (∃̇ φ) ν ≤ᴮ c ⟩)
  (law-∀-lb   : ∀ {k} (φ : Src (suc k)) (ν : Envᴮ k) (σ : Nameᴮ)
              → ⟨ val (∀̇ φ) ν ≤ᴮ val φ (σ ∷ ν) ⟩)
  (law-∀-glb  : ∀ {k} (φ : Src (suc k)) (ν : Envᴮ k) (c : Pt B)
              → ((σ : Nameᴮ) → ⟨ c ≤ᴮ val φ (σ ∷ ν) ⟩)
              → ⟨ c ≤ᴮ val (∀̇ φ) ν ⟩)
  (law-∃∈-ub  : ∀ {k} (j : Fin k) (φ : Src (suc k)) (ν : Envᴮ k) (σ : Nameᴮ)
              → ⟨ (memᴬ (fst σ) (fst (lookup j ν)) ⊓ᴮ val φ (σ ∷ ν))
                  ≤ᴮ val (∃̇∈ (var j) φ) ν ⟩)
  (law-∃∈-lub : ∀ {k} (j : Fin k) (φ : Src (suc k)) (ν : Envᴮ k) (c : Pt B)
              → ((σ : Nameᴮ)
                 → ⟨ (memᴬ (fst σ) (fst (lookup j ν)) ⊓ᴮ val φ (σ ∷ ν))
                     ≤ᴮ c ⟩)
              → ⟨ val (∃̇∈ (var j) φ) ν ≤ᴮ c ⟩)
  (law-∀∈-lb  : ∀ {k} (j : Fin k) (φ : Src (suc k)) (ν : Envᴮ k) (σ : Nameᴮ)
              → ⟨ val (∀̇∈ (var j) φ) ν
                  ≤ᴮ (memᴬ (fst σ) (fst (lookup j ν)) ⇒ᴮ val φ (σ ∷ ν)) ⟩)
  (law-∀∈-glb : ∀ {k} (j : Fin k) (φ : Src (suc k)) (ν : Envᴮ k) (c : Pt B)
              → ((σ : Nameᴮ) → ⟨ c ≤ᴮ (memᴬ (fst σ) (fst (lookup j ν))
                                       ⇒ᴮ val φ (σ ∷ ν)) ⟩)
              → ⟨ c ≤ᴮ val (∀̇∈ (var j) φ) ν ⟩)
  where

  module F = CL.Core iᶠ _⊩ᴮ_ ⊩ᴮ-spec ≼-refl ≼-trans
    ⊩ᴮ-mono ⊩ᴮ-down ⊩ᴮ-reg ⊩ᴮ-⊥ ⊩ᴮ-extend eqᴬ memᴬ val
    law-∈ law-≐ law-∧ law-∨ law-⇒ law-⊥
    law-∃-ub law-∃-lub law-∀-lb law-∀-glb
    law-∃∈-ub law-∃∈-lub law-∀∈-lb law-∀∈-glb

  module AtRelation
    (R : ∀ {n} → Cond → Src n → Envᴮ n → Ω)
    (C : F.ForcingClauses R) where

    module V = K7.ForcedFunctionValues 𝒮 Cond Nameᴮ
      (λ q p → fst q ≼ᶜ fst p) R
      (λ p σ τ → p ⊩ᴮ memᴬ (fst σ) (fst τ))
      (λ p σ τ → p ⊩ᴮ eqᴬ (fst σ) (fst τ))
    open F.ForcingClauses C

    clauses : V.Clauses
    clauses = record
      { at-∈ = λ p a b ν → ⇔toPath (at-∈→ p a b ν) (at-∈← p a b ν)
      ; at-≐ = λ p a b ν → ⇔toPath (at-≐→ p a b ν) (at-≐← p a b ν)
      ; at-⊥ = λ p ν → ⇔toPath (at-⊥ p ν) Empty.rec*
      ; at-∧ = λ p φ ψ ν → ⇔toPath (at-∧→ p φ ψ ν) (λ h → at-∧← p φ ψ ν (fst h) (snd h))
      ; at-∨ = λ p φ ψ ν → ⇔toPath (at-∨→ p φ ψ ν) (at-∨← p φ ψ ν)
      ; at-⇒ = λ p φ ψ ν → ⇔toPath (at-⇒→ p φ ψ ν) (at-⇒← p φ ψ ν)
      ; at-∀ = λ p φ ν → ⇔toPath (at-∀→ p φ ν) (at-∀← p φ ν)
      ; at-∃ = λ p φ ν → ⇔toPath (at-∃→ p φ ν) (at-∃← p φ ν)
      ; at-∀∈ = λ p j φ ν → ⇔toPath (at-∀∈→ p j φ ν) (at-∀∈← p j φ ν)
      ; at-∃∈ = λ p j φ ν → ⇔toPath (at-∃∈→ p j φ ν) (at-∃∈← p j φ ν)
      }

    module Proof = V.AtClauses clauses

  module Actual (lem : LEM ℓ) where
    open F using ( _⊩_[_] )
    module A = AtRelation (λ p φ ν → p ⊩ φ [ ν ]) (F.⊩-clauses lem)
    open A.Proof public using ( pairFo; functionFo; valueBody; valueFo; rename-forcing )
    module Result = A.Proof.AtOrder
      (λ p → ≼-refl (fst p) (snd p))
      (λ r q p → ≼-trans (fst r) (fst q) (fst p) (snd r) (snd q) (snd p))
      F.⊩-mono F.⊩-reg

    forced-function-values : (p : Cond) (f x y z : Nameᴮ)
      → ⟨ p ⊩ functionFo [ f ∷ [] ] ⟩
      → ⟨ p ⊩ valueFo [ x ∷ y ∷ f ∷ [] ] ⟩
      → ⟨ p ⊩ valueFo [ x ∷ z ∷ f ∷ [] ] ⟩
      → ⟨ p ⊩ᴮ eqᴬ (fst y) (fst z) ⟩
    forced-function-values = Result.forced-function-values


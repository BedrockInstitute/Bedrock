{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile
import K4.Algebra
import K4.Implication
import K9.BooleanAtomic
import K9.NameGround
import K10.CohenCompile

module K10.CohenValSeam
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (families : NameKernel.Families 𝒮)
  (accessible : NameKernel.Accessibility 𝒮)
  (images : NameKernel.MemberImage 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (κ w : ZFStructure.S 𝒮)
  (lem : LEM ℓ)
  (paths : (x y : ZFStructure.S 𝒮)
         → (ZFStructure._≈ˢ_ 𝒮 x y) ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; var; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ⊥̇; ∃̇_; ∀̇_; ∃̇∈; ∀̇∈ )
open K4.Algebra 𝒮 using ( Pt ; _≤ᴮ_ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

module NG = K9.NameGround 𝒮 families accessible images pow κ w
  using ( extensional ; ≈ˢ-paths )
module BAT = K9.BooleanAtomic 𝒮 families accessible images pow κ w lem
  using ( B ; module Atomic ; module IC ; module BK )
open K4.Algebra.Lattice BAT.IC.codedLattice using ( _⊓ᴮ_ ; _⊔ᴮ_ ; ⊥ᴮ )
open K4.Implication 𝒮 NG.extensional NG.≈ˢ-paths BAT.B
  BAT.IC.codedLattice BAT.IC.codedComplement using ( _⇒ᴮ_ )
module CC = K10.CohenCompile 𝒮 families accessible images pow κ w lem paths

Src : ℕ → Type ℓ
Src k = Formula (⊥* {ℓ}) k

Nameᴮ : Type ℓ
Nameᴮ = Σ[ x ∈ S ] ⟨ BAT.BK.IsName x ⟩

Envᴮ : ℕ → Type ℓ
Envᴮ k = Vec Nameᴮ k

opaque
  val : ∀ {k} → Src k → Envᴮ k → Pt BAT.B
  val = CC.val

opaque
  unfolding val
  law-∈ : ∀ {k} (i j : Fin k) (ν : Envᴮ k)
        → val (var i ∈̇ var j) ν
          ≡ BAT.Atomic._∈ᴮ_ (fst (lookup i ν)) (fst (lookup j ν))
  law-∈ = CC.law-∈

  law-≐ : ∀ {k} (i j : Fin k) (ν : Envᴮ k)
        → val (var i ≐ var j) ν
          ≡ BAT.Atomic._≈ᴮ_ (fst (lookup i ν)) (fst (lookup j ν))
  law-≐ = CC.law-≐

  law-∧ : ∀ {k} (φ ψ : Src k) (ν : Envᴮ k)
        → val (φ ∧̇ ψ) ν ≡ (val φ ν ⊓ᴮ val ψ ν)
  law-∧ = CC.law-∧

  law-∨ : ∀ {k} (φ ψ : Src k) (ν : Envᴮ k)
        → val (φ ∨̇ ψ) ν ≡ (val φ ν ⊔ᴮ val ψ ν)
  law-∨ = CC.law-∨

  law-⇒ : ∀ {k} (φ ψ : Src k) (ν : Envᴮ k)
        → val (φ ⇒̇ ψ) ν ≡ (val φ ν ⇒ᴮ val ψ ν)
  law-⇒ = CC.law-⇒

  law-⊥ : ∀ {k} (ν : Envᴮ k) → val {k} ⊥̇ ν ≡ ⊥ᴮ
  law-⊥ = CC.law-⊥

  law-∃-ub : ∀ {k} (φ : Src (suc k)) (ν : Envᴮ k) (σ : Nameᴮ)
           → ⟨ val φ (σ ∷ ν) ≤ᴮ val (∃̇ φ) ν ⟩
  law-∃-ub = CC.law-∃-ub

  law-∃-lub : ∀ {k} (φ : Src (suc k)) (ν : Envᴮ k) (c : Pt BAT.B)
            → ((σ : Nameᴮ) → ⟨ val φ (σ ∷ ν) ≤ᴮ c ⟩)
            → ⟨ val (∃̇ φ) ν ≤ᴮ c ⟩
  law-∃-lub = CC.law-∃-lub

  law-∀-lb : ∀ {k} (φ : Src (suc k)) (ν : Envᴮ k) (σ : Nameᴮ)
           → ⟨ val (∀̇ φ) ν ≤ᴮ val φ (σ ∷ ν) ⟩
  law-∀-lb = CC.law-∀-lb

  law-∀-glb : ∀ {k} (φ : Src (suc k)) (ν : Envᴮ k) (c : Pt BAT.B)
            → ((σ : Nameᴮ) → ⟨ c ≤ᴮ val φ (σ ∷ ν) ⟩)
            → ⟨ c ≤ᴮ val (∀̇ φ) ν ⟩
  law-∀-glb = CC.law-∀-glb

  law-∃∈-ub : ∀ {k} (i : Fin k) (φ : Src (suc k)) (ν : Envᴮ k) (σ : Nameᴮ)
            → ⟨ (BAT.Atomic._∈ᴮ_ (fst σ) (fst (lookup i ν)) ⊓ᴮ val φ (σ ∷ ν))
                ≤ᴮ val (∃̇∈ (var i) φ) ν ⟩
  law-∃∈-ub = CC.law-∃∈-ub

  law-∃∈-lub : ∀ {k} (i : Fin k) (φ : Src (suc k)) (ν : Envᴮ k) (c : Pt BAT.B)
             → ((σ : Nameᴮ)
                → ⟨ (BAT.Atomic._∈ᴮ_ (fst σ) (fst (lookup i ν)) ⊓ᴮ val φ (σ ∷ ν))
                    ≤ᴮ c ⟩)
             → ⟨ val (∃̇∈ (var i) φ) ν ≤ᴮ c ⟩
  law-∃∈-lub = CC.law-∃∈-lub

  law-∀∈-lb : ∀ {k} (i : Fin k) (φ : Src (suc k)) (ν : Envᴮ k) (σ : Nameᴮ)
            → ⟨ val (∀̇∈ (var i) φ) ν
                ≤ᴮ (BAT.Atomic._∈ᴮ_ (fst σ) (fst (lookup i ν)) ⇒ᴮ val φ (σ ∷ ν)) ⟩
  law-∀∈-lb = CC.law-∀∈-lb

  law-∀∈-glb : ∀ {k} (i : Fin k) (φ : Src (suc k)) (ν : Envᴮ k) (c : Pt BAT.B)
             → ((σ : Nameᴮ)
                → ⟨ c ≤ᴮ (BAT.Atomic._∈ᴮ_ (fst σ) (fst (lookup i ν))
                     ⇒ᴮ val φ (σ ∷ ν)) ⟩)
             → ⟨ c ≤ᴮ val (∀̇∈ (var i) φ) ν ⟩
  law-∀∈-glb = CC.law-∀∈-glb

{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile
import CardinalBridge
import Cubical.Data.Empty as Empty
import K4.Algebra
import K4.Implication
import K9.BooleanAtomic
import K10.CohenCompile

module K10.CohenBooleanInjBot
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
open import FOL.Syntax using ( var ; _∈̇_ ; _≐_ ; _∧̇_ ; _⇒̇_ ; ∃̇_ ; ∀̇_ ; ∀̇∈ )
open import FOL.Manipulation.ConstantOccurrences using ( module ZeroOccurrences )
import CardinalBridge

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

module CC = K10.CohenCompile 𝒮 families accessible images pow κ w lem paths
module BAT = K9.BooleanAtomic 𝒮 families accessible images pow κ w lem
  using ( B ; module Atomic ; module IC ; module Checked )
module CB = CardinalBridge 𝒮
module ZO = ZeroOccurrences S

open CC public using ( Src ; Nameᴮ ; Envᴮ )
open BAT using ( module IC ; module Checked )
open CC.NG using ( extensional ; ≈ˢ-paths )
open K4.Algebra 𝒮 using ( Pt ; ≤ᴮ-refl ; _≤ᴮ_ )
open K4.Algebra.Lattice IC.codedLattice using ( _⊓ᴮ_ ; ⊥ᴮ ; ⊤ᴮ )
open K4.Implication 𝒮 extensional ≈ˢ-paths BAT.B
  IC.codedLattice IC.codedComplement
  using ( ≤⊥→≡⊥ ; ≤ᴮ-antisym ; ⊤-greatest ; _⇒ᴮ_ )

⊤B : Pt BAT.B
⊤B = ⊤ᴮ

⊥B : Pt BAT.B
⊥B = ⊥ᴮ

emptyEnv : Envᴮ 0
emptyEnv = []

checkNm : S → Nameᴮ
checkNm a = Checked.check a , Checked.check-name a

injSrc : Src 2
injSrc = ZO.erase CB.Injectableφ refl

injBody : Src 3
injBody = ZO.erase CB.IsInjectionφ refl

inj-shape : injSrc ≡ ∃̇ injBody
inj-shape = refl

opaque
  val : ∀ {k} → Src k → Envᴮ k → Pt BAT.B
  val = CC.val

opaque
  unfolding val
  law-∃-lub : ∀ {k} (φ : Src (suc k)) (ν : Envᴮ k) (c : Pt BAT.B)
            → ((σ : Nameᴮ) → ⟨ val φ (σ ∷ ν) ≤ᴮ c ⟩)
            → ⟨ val (∃̇ φ) ν ≤ᴮ c ⟩
  law-∃-lub = CC.law-∃-lub

  law-∃-ub : ∀ {k} (φ : Src (suc k)) (ν : Envᴮ k) (σ : Nameᴮ)
           → ⟨ val φ (σ ∷ ν) ≤ᴮ val (∃̇ φ) ν ⟩
  law-∃-ub = CC.law-∃-ub

  law-∈ : ∀ {k} (i j : Fin k) (ν : Envᴮ k)
        → val (var i ∈̇ var j) ν
          ≡ BAT.Atomic._∈ᴮ_ (fst (lookup i ν)) (fst (lookup j ν))
  law-∈ = CC.law-∈

  law-∧ : ∀ {k} (φ ψ : Src k) (ν : Envᴮ k)
        → val (φ ∧̇ ψ) ν ≡ (val φ ν ⊓ᴮ val ψ ν)
  law-∧ = CC.law-∧

  law-⇒ : ∀ {k} (φ ψ : Src k) (ν : Envᴮ k)
        → val (φ ⇒̇ ψ) ν ≡ (val φ ν ⇒ᴮ val ψ ν)
  law-⇒ = CC.law-⇒

  law-∀∈-lb : ∀ {k} (i : Fin k) (φ : Src (suc k)) (ν : Envᴮ k) (σ : Nameᴮ)
            → ⟨ val (∀̇∈ (var i) φ) ν
                ≤ᴮ (BAT.Atomic._∈ᴮ_ (fst σ) (fst (lookup i ν))
                     ⇒ᴮ val φ (σ ∷ ν)) ⟩
  law-∀∈-lb = CC.law-∀∈-lb

  law-∀-lb : ∀ {k} (φ : Src (suc k)) (ν : Envᴮ k) (σ : Nameᴮ)
           → ⟨ val (∀̇ φ) ν ≤ᴮ val φ (σ ∷ ν) ⟩
  law-∀-lb = CC.law-∀-lb

  law-≐ : ∀ {k} (i j : Fin k) (ν : Envᴮ k)
        → val (var i ≐ var j) ν
          ≡ BAT.Atomic._≈ᴮ_ (fst (lookup i ν)) (fst (lookup j ν))
  law-≐ = CC.law-≐

inj-bot-from : (a b : Nameᴮ)
  → ((σ : Nameᴮ) → val injBody (σ ∷ a ∷ b ∷ emptyEnv) ≡ ⊥B)
  → val injSrc (a ∷ b ∷ emptyEnv) ≡ ⊥B
inj-bot-from a b hyp =
  ≤⊥→≡⊥ (val injSrc (a ∷ b ∷ emptyEnv))
    (subst (λ φ → ⟨ val φ (a ∷ b ∷ emptyEnv) ≤ᴮ ⊥B ⟩) (sym inj-shape)
      (law-∃-lub injBody (a ∷ b ∷ emptyEnv) ⊥B λ σ →
        subst (λ z → ⟨ z ≤ᴮ ⊥B ⟩) (sym (hyp σ))
          (≤ᴮ-refl ⊥B)))

inj-top-from : (a b σ : Nameᴮ)
  → val injBody (σ ∷ a ∷ b ∷ emptyEnv) ≡ ⊤B
  → val injSrc (a ∷ b ∷ emptyEnv) ≡ ⊤B
inj-top-from a b σ body-top =
  ≤ᴮ-antisym (⊤-greatest (val injSrc (a ∷ b ∷ emptyEnv)))
    (subst (λ φ → ⟨ ⊤B ≤ᴮ val φ (a ∷ b ∷ emptyEnv) ⟩) (sym inj-shape)
      (subst (λ z → ⟨ z ≤ᴮ val (∃̇ injBody) (a ∷ b ∷ emptyEnv) ⟩) body-top
        (law-∃-ub injBody (a ∷ b ∷ emptyEnv) σ)))

cardinal-no-inj : (μ : S) → ⟨ CB.isCardinal μ ⟩ → ⟨ w ∈ˢ μ ⟩
  → ⟨ CB.injectable μ w ⟩ → Empty.⊥
cardinal-no-inj μ (_ , hno) hmem hinj = hno w hmem hinj

BooleanResidue : S → Type ℓ
BooleanResidue μ =
  (σ : Nameᴮ) → val injBody (σ ∷ checkNm μ ∷ checkNm w ∷ emptyEnv) ≡ ⊥B

module AtCardinal
  (ω₁ : S)
  (hω₁ : ⟨ CB.isCardinal ω₁ ⟩)
  (hw₁ : ⟨ w ∈ˢ ω₁ ⟩)
  where

  xw-env : Envᴮ 2
  xw-env = checkNm ω₁ ∷ checkNm w ∷ emptyEnv

  no-ground-injection : ⟨ CB.injectable ω₁ w ⟩ → Empty.⊥
  no-ground-injection = cardinal-no-inj ω₁ hω₁ hw₁

  module FromResidue (residue : BooleanResidue ω₁) where

    inj-xw-bot : val injSrc xw-env ≡ ⊥B
    inj-xw-bot = inj-bot-from (checkNm ω₁) (checkNm w) residue

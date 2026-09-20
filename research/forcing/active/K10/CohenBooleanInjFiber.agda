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
import K7.CardinalOrder
import K7.ChainConditions
import K9.NameGround
import K10.CohenBooleanInjCcc
import K10.CohenBooleanInjForce

module K10.CohenBooleanInjFiber
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (families : NameKernel.Families 𝒮)
  (accessible : NameKernel.Accessibility 𝒮)
  (images : NameKernel.MemberImage 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (find : OrdinaryProfile.FoundationInduction 𝒮)
  (κ w : ZFStructure.S 𝒮)
  (lem : LEM ℓ)
  (hw : ⟨ CardinalBridge.isOmega 𝒮 w ⟩)
  (paths : (x y : ZFStructure.S 𝒮)
         → (ZFStructure._≈ˢ_ 𝒮 x y) ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import OrdinaryProfile 𝒮 using ( ChoiceSet )
open import CodedVocabulary 𝒮 using ( subsetΔ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

module Force = K10.CohenBooleanInjForce 𝒮 families accessible images pow κ w lem paths
module Ccc = K10.CohenBooleanInjCcc 𝒮 families accessible images pow find
  κ w lem hw paths
module NG = K9.NameGround 𝒮 families accessible images pow κ w
  using ( extensional ; ≈ˢ-paths ; hasPair ; hasUnion ; hasSeparation ; module C )
module CB = CardinalBridge 𝒮
module CH = K7.ChainConditions 𝒮 NG.extensional NG.≈ˢ-paths
  using ( CCC₂ᴵ ; ccc-use ; antichainΔ )
open NameKernel.Families families using ( hasCollect )
module CO = K7.CardinalOrder.Order 𝒮 NG.extensional
  (λ x y z e → cong (_∈ˢ z) (subst ⟨_⟩ (NG.≈ˢ-paths x y) e))
  (λ x y z e → cong (x ∈ˢ_) (subst ⟨_⟩ (NG.≈ˢ-paths y z) e))

open Force using ( Nameᴮ ; val ; injBody ; injSrc ; checkNm ; emptyEnv
                 ; BooleanResidue ; i ; Cond )
open K4.Algebra 𝒮 using ( _≤ᴮ_ )

CollapseWitness : (ω₁ : S) → Type ℓ
CollapseWitness ω₁ =
  (σ : Nameᴮ) (p : Cond)
  → ⟨ i p ≤ᴮ val injBody (σ ∷ checkNm ω₁ ∷ checkNm w ∷ emptyEnv) ⟩
  → ⟨ CB.injectable ω₁ w ⟩

module AtCardinal
  (ω₁ : S)
  (hω₁ : ⟨ CB.isCardinal ω₁ ⟩)
  (hw₁ : ⟨ w ∈ˢ ω₁ ⟩)
  (choice : ChoiceSet)
  where

  open Force.AtCardinal ω₁ hω₁ hw₁
  open Ccc.Over choice using ( cohen-ccc )

  fiber-countable : (d : S)
    → ⟨ subsetΔ d NG.C.carrier ⟩
    → ⟨ CH.antichainΔ NG.C.carrier NG.C.order d ⟩
    → ⟨ CB.injectable d w ⟩
  fiber-countable d sub ac =
    CH.ccc-use NG.C.carrier NG.C.order w d cohen-ccc sub ac

  collapse-from-antichain : (d : S)
    → ⟨ subsetΔ d NG.C.carrier ⟩
    → ⟨ CH.antichainΔ NG.C.carrier NG.C.order d ⟩
    → ⟨ CB.injectable ω₁ d ⟩
    → ⟨ CB.injectable ω₁ w ⟩
  collapse-from-antichain d sub ac inj =
    CO.injectable-trans NG.hasSeparation hasCollect NG.hasPair
      ω₁ d w inj (fiber-countable d sub ac)

  ω-fiber-covering : CollapseWitness ω₁
    → (σ : Nameᴮ) (p : Cond)
    → ⟨ i p ≤ᴮ val injBody (env-of σ) ⟩
    → Empty.⊥
  ω-fiber-covering collapse σ p hp =
    Force.IB.cardinal-no-inj ω₁ hω₁ hw₁ (collapse σ p hp)

  module FromCovering (collapse : CollapseWitness ω₁) where

    unforced : (σ : Nameᴮ) (p : Cond)
             → ⟨ i p ≤ᴮ val injBody (env-of σ) ⟩ → Empty.⊥
    unforced = ω-fiber-covering collapse

    open FromUnforced unforced public

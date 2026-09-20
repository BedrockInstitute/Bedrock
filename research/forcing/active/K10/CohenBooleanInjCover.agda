{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile
import CardinalBridge
import Cubical.Data.Empty as Empty
open import Cubical.Data.Sum using ( _⊎_ ; inl ; inr )
import Cubical.HITs.PropositionalTruncation as PT
import K4.Algebra
import K4.Implication
import K5.Frame
import K9.BooleanNameGround
import K10.CohenBooleanCheckMem
import K10.CohenBooleanInjBot

module K10.CohenBooleanInjCover
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
open import FOL.Syntax using ( var ; _∈̇_ ; _∧̇_ ; ∃̇_ ; ∀̇∈ )
open import FOL.Manipulation.ConstantOccurrences using ( module ZeroOccurrences )
open import FOL.Manipulation.Renaming using ( renameFo )
import CardinalBridge

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open PT using ( ∣_∣₁ )

module IB = K10.CohenBooleanInjBot 𝒮 families accessible images pow κ w lem paths
module Mem = K10.CohenBooleanCheckMem 𝒮 families accessible images pow κ w lem
module BNG = K9.BooleanNameGround 𝒮 families accessible images pow κ w lem
module CB = CardinalBridge 𝒮
module ZO = ZeroOccurrences S

open IB using ( Src ; Nameᴮ ; Envᴮ ; val ; emptyEnv ; checkNm ; injSrc ; injBody
              ; inj-bot-from ; BooleanResidue ; ⊥B ; ⊤B
              ; law-∧ ; law-∀∈-lb ; law-∈ )
open IB.BAT using ( module IC ; module Atomic ; module Checked )
open IB.CC.NG using ( extensional ; ≈ˢ-paths )
open K4.Algebra 𝒮 using ( Pt ; _≤ᴮ_ ; ≤ᴮ-refl ; ⊆ˢ-trans ; isSetPt )
open K4.Algebra.Lattice IC.codedLattice
  using ( _⊓ᴮ_ ; ⊓-lb₁ ; ⊓-lb₂ ; ⊥ᴮ ; ⊤ᴮ )
open K4.Implication 𝒮 extensional ≈ˢ-paths IB.BAT.B
  IC.codedLattice IC.codedComplement
  using ( ≤⊥→≡⊥ ; _⇒ᴮ_ ; ⇒ᴮ-⊤ˡ )
open K5.Frame.Poset 𝒮 BNG.NG.C.carrier BNG.NG.C.order using ( Cond )
open K5.Frame.Poset.ForcingBase (BNG.Base.codedBase lem)
  using ( i ; i-dense )

funSrc : Src 3
funSrc = ZO.erase (renameFo CB.inj-fun CB.IsFunctionφ) refl

domSrc : Src 3
domSrc = ZO.erase CB.InjDomφ refl

ranSrc : Src 3
ranSrc = ZO.erase CB.InjRanφ refl

pairSrc : Src 3
pairSrc = ZO.erase CB.InjPairφ refl

body-split : injBody ≡ (funSrc ∧̇ (domSrc ∧̇ (ranSrc ∧̇ pairSrc)))
body-split = refl

domExists : Src 4
domExists = ZO.erase
  (∃̇ (∃̇ ((var zero ∈̇ var (suc (suc (suc zero))))
        ∧̇ (renameFo CB.inj-dom CB.PairφK))))
  refl

dom-shape : domSrc ≡ ∀̇∈ (var (suc zero)) domExists
dom-shape = refl

body-le-dom : (σ a b : Nameᴮ)
  → ⟨ val injBody (σ ∷ a ∷ b ∷ emptyEnv)
      ≤ᴮ val domSrc (σ ∷ a ∷ b ∷ emptyEnv) ⟩
body-le-dom σ a b =
  subst (λ φ → ⟨ val φ env ≤ᴮ val domSrc env ⟩) (sym body-split)
    (subst (λ z → ⟨ z ≤ᴮ val domSrc env ⟩) (sym (law-∧ funSrc rest env))
      (⊆ˢ-trans (⊓-lb₂ (val funSrc env) (val rest env))
        (subst (λ z → ⟨ z ≤ᴮ val domSrc env ⟩)
          (sym (law-∧ domSrc tail env))
          (⊓-lb₁ (val domSrc env) (val tail env)))))
  where
  env = σ ∷ a ∷ b ∷ emptyEnv
  rest : Src 3
  rest = domSrc ∧̇ (ranSrc ∧̇ pairSrc)
  tail : Src 3
  tail = ranSrc ∧̇ pairSrc

dom-at-check : (σ : Nameᴮ) (ξ ω₁ : S) → ⟨ ξ ∈ˢ ω₁ ⟩
  → ⟨ val domSrc (σ ∷ checkNm ω₁ ∷ checkNm w ∷ emptyEnv)
      ≤ᴮ val domExists (checkNm ξ ∷ σ ∷ checkNm ω₁ ∷ checkNm w ∷ emptyEnv) ⟩
dom-at-check σ ξ ω₁ hξ =
  subst (λ z → ⟨ val domSrc env ≤ᴮ z ⟩) step2 step1
  where
  env = σ ∷ checkNm ω₁ ∷ checkNm w ∷ emptyEnv
  exists = val domExists (checkNm ξ ∷ env)
  mem = Atomic._∈ᴮ_ (fst (checkNm ξ)) (fst (checkNm ω₁))
  mem-top : mem ≡ ⊤B
  mem-top = Mem.check-∈-top ξ ω₁ hξ
  step1 : ⟨ val domSrc env ≤ᴮ (mem ⇒ᴮ exists) ⟩
  step1 =
    subst (λ φ → ⟨ val φ env ≤ᴮ (mem ⇒ᴮ exists) ⟩) (sym dom-shape)
      (law-∀∈-lb (suc zero) domExists env (checkNm ξ))
  step2 : (mem ⇒ᴮ exists) ≡ exists
  step2 = cong (_⇒ᴮ exists) mem-top ∙ ⇒ᴮ-⊤ˡ exists

body-bot-from-unforced : (σ : Nameᴮ) (ω₁ : S)
  → ((p : Cond)
     → ⟨ i p ≤ᴮ val injBody (σ ∷ checkNm ω₁ ∷ checkNm w ∷ emptyEnv) ⟩
     → Empty.⊥)
  → val injBody (σ ∷ checkNm ω₁ ∷ checkNm w ∷ emptyEnv) ≡ ⊥B
body-bot-from-unforced σ ω₁ unforced =
  decide (lem ((I ≡ ⊥B) , isSetPt IB.BAT.B I ⊥B))
  where
  I = val injBody (σ ∷ checkNm ω₁ ∷ checkNm w ∷ emptyEnv)
  decide : (I ≡ ⊥B) ⊎ ((I ≡ ⊥B) → Empty.⊥) → I ≡ ⊥B
  decide (inl eq) = eq
  decide (inr neq) =
    Empty.rec (PT.rec Empty.isProp⊥
      (λ { (p , hp) → unforced p hp })
      (i-dense I (λ e → lift (neq e))))

module AtCardinal
  (ω₁ : S)
  (hω₁ : ⟨ CB.isCardinal ω₁ ⟩)
  (hw₁ : ⟨ w ∈ˢ ω₁ ⟩)
  where

  env-of : Nameᴮ → Envᴮ 3
  env-of σ = σ ∷ checkNm ω₁ ∷ checkNm w ∷ emptyEnv

  module FromUnforced
    (unforced : (σ : Nameᴮ) (p : Cond)
              → ⟨ i p ≤ᴮ val injBody (env-of σ) ⟩ → Empty.⊥)
    where

    residue : BooleanResidue ω₁
    residue σ = body-bot-from-unforced σ ω₁ (unforced σ)

    inj-xw-bot : val injSrc (checkNm ω₁ ∷ checkNm w ∷ emptyEnv) ≡ ⊥B
    inj-xw-bot = inj-bot-from (checkNm ω₁) (checkNm w) residue


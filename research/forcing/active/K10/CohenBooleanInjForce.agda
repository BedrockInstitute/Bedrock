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
import K9.BooleanAtomic
import K10.CohenBooleanInjBot

module K10.CohenBooleanInjForce
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
open import FOL.Syntax using ( _∧̇_ )
open import CodedVocabulary 𝒮 using ( refinesΔ )
open import FOL.Manipulation.ConstantOccurrences using ( module ZeroOccurrences )
open import FOL.Manipulation.Renaming using ( renameFo )
import CardinalBridge

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

module IB = K10.CohenBooleanInjBot 𝒮 families accessible images pow κ w lem paths
module BAT = K9.BooleanAtomic 𝒮 families accessible images pow κ w lem
  using ( B ; module IC ; module Base ; module NG )
module CB = CardinalBridge 𝒮
module ZO = ZeroOccurrences S

open IB public using ( Src ; Nameᴮ ; Envᴮ ; val ; emptyEnv ; checkNm ; injSrc ; injBody
              ; inj-bot-from ; BooleanResidue ; ⊥B ; ⊤B ; law-∧ ; law-⇒ ; law-∀∈-lb
              ; law-∀-lb ; law-≐ ; cardinal-no-inj )
open BAT using ( module IC ; module Base ; module NG )
open IB.CC.NG using ( extensional ; ≈ˢ-paths )
open K4.Algebra 𝒮 using ( Pt ; _≤ᴮ_ ; ⊆ˢ-trans ; isSetPt )
open K4.Algebra.Lattice IC.codedLattice
  using ( _⊓ᴮ_ ; ⊓-lb₁ ; ⊓-lb₂ ; ⊥ᴮ )
open K5.Frame.Poset 𝒮 NG.C.carrier NG.C.order public using ( Cond )
open K5.Frame.Poset.ForcingBase (Base.codedBase lem)
  public using ( i ; i-dense ; i-nonzero ; i-mono ; below ; below-in ; below-out )

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

body-le-pair : (σ a b : Nameᴮ)
  → ⟨ val injBody (σ ∷ a ∷ b ∷ emptyEnv)
      ≤ᴮ val pairSrc (σ ∷ a ∷ b ∷ emptyEnv) ⟩
body-le-pair σ a b =
  subst (λ φ → ⟨ val φ env ≤ᴮ val pairSrc env ⟩) (sym body-split)
    (subst (λ z → ⟨ z ≤ᴮ val pairSrc env ⟩) (sym (law-∧ funSrc rest env))
      (⊆ˢ-trans (⊓-lb₂ (val funSrc env) (val rest env))
        (subst (λ z → ⟨ z ≤ᴮ val pairSrc env ⟩)
          (sym (law-∧ domSrc tail env))
          (⊆ˢ-trans (⊓-lb₂ (val domSrc env) (val tail env))
            (subst (λ z → ⟨ z ≤ᴮ val pairSrc env ⟩)
              (sym (law-∧ ranSrc pairSrc env))
              (⊓-lb₂ (val ranSrc env) (val pairSrc env)))))))
  where
  env = σ ∷ a ∷ b ∷ emptyEnv
  rest : Src 3
  rest = domSrc ∧̇ (ranSrc ∧̇ pairSrc)
  tail : Src 3
  tail = ranSrc ∧̇ pairSrc

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

pair-at-r : (σ : Nameᴮ) (pC : Cond) (ω₁ : S)
  (forced : ⟨ i pC ≤ᴮ val injBody (σ ∷ checkNm ω₁ ∷ checkNm w ∷ emptyEnv) ⟩)
  (r : S) (r∈c : ⟨ r ∈ˢ NG.C.carrier ⟩)
  (r≼p : ⟨ refinesΔ NG.C.order r (fst pC) ⟩)
  → ⟨ i (r , r∈c) ≤ᴮ val pairSrc (σ ∷ checkNm ω₁ ∷ checkNm w ∷ emptyEnv) ⟩
pair-at-r σ pC ω₁ forced r r∈c r≼p =
  ⊆ˢ-trans (i-mono pC (r , r∈c) r≼p)
    (⊆ˢ-trans forced (body-le-pair σ (checkNm ω₁) (checkNm w)))

body-bot-from-unforced : (σ : Nameᴮ) (ω₁ : S)
  → ((p : Cond)
     → ⟨ i p ≤ᴮ val injBody (σ ∷ checkNm ω₁ ∷ checkNm w ∷ emptyEnv) ⟩
     → Empty.⊥)
  → val injBody (σ ∷ checkNm ω₁ ∷ checkNm w ∷ emptyEnv) ≡ ⊥B
body-bot-from-unforced σ ω₁ unforced =
  decide (lem ((I ≡ ⊥B) , isSetPt BAT.B I ⊥B))
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

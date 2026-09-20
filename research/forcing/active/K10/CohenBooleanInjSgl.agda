{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile
import CardinalBridge
import Cubical.HITs.PropositionalTruncation as PT
import K4.Algebra
import K4.Implication
import K9.BooleanAtomic
import K9.BooleanNameGround
import K9.NameGround
import K10.CohenValSeam
import K10.CohenBooleanCheckMem

-- IsSingletonφ and IsPairφ at check names. Both are Δ₀; this file does not
-- instantiate check-Δ₀-val. No CCC, Force, Pipe, Miximal, or OmegaTop.

module K10.CohenBooleanInjSgl
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
open import FOL.Syntax using ( var ; _∈̇_ ; _≐_ ; _∧̇_ ; _∨̇_ ; ∀̇∈ )
open import FOL.Manipulation.ConstantOccurrences using ( module ZeroOccurrences )
open import Cubical.Data.Sum using ( _⊎_ ; inl ; inr )
import CardinalBridge

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open PT using ( ∣_∣₁ )

module NG = K9.NameGround 𝒮 families accessible images pow κ w
  using ( extensional ; ≈ˢ-paths )
module BAT = K9.BooleanAtomic 𝒮 families accessible images pow κ w lem
  using ( B ; module Atomic ; module IC ; module Laws )
open K4.Algebra 𝒮 using ( Pt ; _≤ᴮ_ ; ⊆ˢ-trans )
open K4.Algebra.Lattice BAT.IC.codedLattice
  using ( _⊓ᴮ_ ; _⊔ᴮ_ ; ⊤ᴮ ; ⊔-ub₁ ; ⊔-ub₂ )
open K4.Implication 𝒮 NG.extensional NG.≈ˢ-paths BAT.B
  BAT.IC.codedLattice BAT.IC.codedComplement
  using ( ≤ᴮ-antisym ; ⊤-greatest ; _⇒ᴮ_ ; ⇒ᴮ-curry ; ⊓-⊤ ; ⊓-comm )
module VS = K10.CohenValSeam 𝒮 families accessible images pow κ w lem paths
module BNG = K9.BooleanNameGround 𝒮 families accessible images pow κ w lem
module CM = K10.CohenBooleanCheckMem 𝒮 families accessible images pow κ w lem
module CB = CardinalBridge 𝒮
module ZO = ZeroOccurrences S
open BAT.Atomic using () renaming ( _∈ᴮ_ to mem ; _≈ᴮ_ to eq )

checkNm : S → VS.Nameᴮ
checkNm a = BNG.Checked.check a , BNG.Checked.check-name a

≈→≡ : {a b : S} → ⟨ a ≈ˢ b ⟩ → a ≡ b
≈→≡ {a} {b} = subst ⟨_⟩ (NG.≈ˢ-paths a b)

check-eq-top : {a b : S} → ⟨ a ≈ˢ b ⟩
  → eq (BNG.Checked.check a) (BNG.Checked.check b) ≡ ⊤ᴮ
check-eq-top {a} {b} h =
  subst (λ z → eq (BNG.Checked.check a) (BNG.Checked.check z) ≡ ⊤ᴮ)
    (≈→≡ h) (BAT.Laws.≈ᴮ-refl (BNG.Checked.check a))

eq-from-check : (σ : VS.Nameᴮ) (b x : S) → ⟨ b ≈ˢ x ⟩
  → ⟨ eq (fst σ) (BNG.Checked.check b)
      ≤ᴮ eq (fst σ) (BNG.Checked.check x) ⟩
eq-from-check σ b x heq =
  subst (λ z → ⟨ z ≤ᴮ eq (fst σ) (BNG.Checked.check x) ⟩)
    (⊓-⊤ (eq (fst σ) (BNG.Checked.check b)))
    (subst (λ z → ⟨ (eq (fst σ) (BNG.Checked.check b) ⊓ᴮ z)
                    ≤ᴮ eq (fst σ) (BNG.Checked.check x) ⟩)
      (check-eq-top heq)
      (BAT.Laws.≈ᴮ-trans (fst σ) (BNG.Checked.check b) (BNG.Checked.check x)))

sglSrc : VS.Src 2
sglSrc = ZO.erase CB.IsSingletonφ refl

sglMemberφ : VS.Src 2
sglMemberφ = var (suc zero) ∈̇ var zero

sglOnlyφ : VS.Src 2
sglOnlyφ = ∀̇∈ (var zero) (var zero ≐ var (suc (suc zero)))

sgl-shape : sglSrc ≡ (sglMemberφ ∧̇ sglOnlyφ)
sgl-shape = refl

sglEnv : S → S → VS.Envᴮ 2
sglEnv t x = checkNm t ∷ checkNm x ∷ []

sgl-member-top : (t x : S) → ⟨ x ∈ˢ t ⟩
  → VS.val sglMemberφ (sglEnv t x) ≡ ⊤ᴮ
sgl-member-top t x hin =
  VS.law-∈ (suc zero) zero (sglEnv t x) ∙ CM.check-∈-top x t hin

sgl-only-top : (t x : S)
  → ⟨ ⋀ S (λ u → (u ∈ˢ t) ⇒ (u ≈ˢ x)) ⟩
  → VS.val sglOnlyφ (sglEnv t x) ≡ ⊤ᴮ
sgl-only-top t x honly = ≤ᴮ-antisym
  (⊤-greatest (VS.val sglOnlyφ (sglEnv t x)))
  (VS.law-∀∈-glb zero (var zero ≐ var (suc (suc zero))) (sglEnv t x) ⊤ᴮ λ σ →
    subst (λ b → ⟨ ⊤ᴮ ≤ᴮ (mem (fst σ) (BNG.Checked.check t) ⇒ᴮ b) ⟩)
      (sym (VS.law-≐ zero (suc (suc zero)) (σ ∷ sglEnv t x)))
      (⇒ᴮ-curry ⊤ᴮ (mem (fst σ) (BNG.Checked.check t))
        (eq (fst σ) (BNG.Checked.check x))
        (subst (λ z → ⟨ z ≤ᴮ eq (fst σ) (BNG.Checked.check x) ⟩)
          (sym (⊓-comm ⊤ᴮ (mem (fst σ) (BNG.Checked.check t))
                ∙ ⊓-⊤ (mem (fst σ) (BNG.Checked.check t))))
          (CM.check-∈-lub t (fst σ) (eq (fst σ) (BNG.Checked.check x))
            (λ a ha → eq-from-check σ a x (honly a ha))))))

sgl-at-checks : (t x : S) → ⟨ CB.isSingleton t x ⟩
  → VS.val sglSrc (sglEnv t x) ≡ ⊤ᴮ
sgl-at-checks t x (hin , honly) =
  cong (λ φ → VS.val φ (sglEnv t x)) sgl-shape
  ∙ VS.law-∧ sglMemberφ sglOnlyφ (sglEnv t x)
  ∙ cong₂ _⊓ᴮ_ (sgl-member-top t x hin) (sgl-only-top t x honly)
  ∙ ⊓-⊤ ⊤ᴮ

pairSrc : VS.Src 3
pairSrc = ZO.erase CB.IsPairφ refl

pairLeftφ : VS.Src 3
pairLeftφ = var (suc zero) ∈̇ var zero

pairRightφ : VS.Src 3
pairRightφ = var (suc (suc zero)) ∈̇ var zero

pairOnlyφ : VS.Src 3
pairOnlyφ = ∀̇∈ (var zero)
  ((var zero ≐ var (suc (suc zero)))
    ∨̇ (var zero ≐ var (suc (suc (suc zero)))))

pair-shape : pairSrc ≡ (pairLeftφ ∧̇ (pairRightφ ∧̇ pairOnlyφ))
pair-shape = refl

pairEnv : S → S → S → VS.Envᴮ 3
pairEnv t x y = checkNm t ∷ checkNm x ∷ checkNm y ∷ []

pair-left-top : (t x y : S) → ⟨ x ∈ˢ t ⟩
  → VS.val pairLeftφ (pairEnv t x y) ≡ ⊤ᴮ
pair-left-top t x y hin =
  VS.law-∈ (suc zero) zero (pairEnv t x y) ∙ CM.check-∈-top x t hin

pair-right-top : (t x y : S) → ⟨ y ∈ˢ t ⟩
  → VS.val pairRightφ (pairEnv t x y) ≡ ⊤ᴮ
pair-right-top t x y hin =
  VS.law-∈ (suc (suc zero)) zero (pairEnv t x y) ∙ CM.check-∈-top y t hin

pair-only-top : (t x y : S)
  → ⟨ ⋀ S (λ u → (u ∈ˢ t) ⇒ ((u ≈ˢ x) ⊔ (u ≈ˢ y))) ⟩
  → VS.val pairOnlyφ (pairEnv t x y) ≡ ⊤ᴮ
pair-only-top t x y honly = ≤ᴮ-antisym
  (⊤-greatest (VS.val pairOnlyφ (pairEnv t x y)))
  (VS.law-∀∈-glb zero
    ((var zero ≐ var (suc (suc zero)))
      ∨̇ (var zero ≐ var (suc (suc (suc zero)))))
    (pairEnv t x y) ⊤ᴮ λ σ →
    subst (λ b → ⟨ ⊤ᴮ ≤ᴮ (mem (fst σ) (BNG.Checked.check t) ⇒ᴮ b) ⟩)
      (sym (VS.law-∨ (var zero ≐ var (suc (suc zero)))
        (var zero ≐ var (suc (suc (suc zero)))) (σ ∷ pairEnv t x y)
        ∙ cong₂ _⊔ᴮ_
          (VS.law-≐ zero (suc (suc zero)) (σ ∷ pairEnv t x y))
          (VS.law-≐ zero (suc (suc (suc zero))) (σ ∷ pairEnv t x y))))
      (⇒ᴮ-curry ⊤ᴮ (mem (fst σ) (BNG.Checked.check t))
        (eq (fst σ) (BNG.Checked.check x)
          ⊔ᴮ eq (fst σ) (BNG.Checked.check y))
        (subst (λ z → ⟨ z ≤ᴮ (eq (fst σ) (BNG.Checked.check x)
                              ⊔ᴮ eq (fst σ) (BNG.Checked.check y)) ⟩)
          (sym (⊓-comm ⊤ᴮ (mem (fst σ) (BNG.Checked.check t))
                ∙ ⊓-⊤ (mem (fst σ) (BNG.Checked.check t))))
          (CM.check-∈-lub t (fst σ)
            (eq (fst σ) (BNG.Checked.check x)
              ⊔ᴮ eq (fst σ) (BNG.Checked.check y))
            (λ a ha → PT.rec
              (snd (eq (fst σ) (BNG.Checked.check a)
                    ≤ᴮ (eq (fst σ) (BNG.Checked.check x)
                      ⊔ᴮ eq (fst σ) (BNG.Checked.check y))))
              (choose σ a)
              (honly a ha))))))
  where
  choose : (σ : VS.Nameᴮ) (a : S)
    → ⟨ a ≈ˢ x ⟩ ⊎ ⟨ a ≈ˢ y ⟩
    → ⟨ eq (fst σ) (BNG.Checked.check a)
        ≤ᴮ (eq (fst σ) (BNG.Checked.check x)
          ⊔ᴮ eq (fst σ) (BNG.Checked.check y)) ⟩
  choose σ a (inl heq) = ⊆ˢ-trans (eq-from-check σ a x heq)
    (⊔-ub₁ (eq (fst σ) (BNG.Checked.check x))
      (eq (fst σ) (BNG.Checked.check y)))
  choose σ a (inr heq) = ⊆ˢ-trans (eq-from-check σ a y heq)
    (⊔-ub₂ (eq (fst σ) (BNG.Checked.check x))
      (eq (fst σ) (BNG.Checked.check y)))

pair-at-checks : (t x y : S) → ⟨ CB.isPair t x y ⟩
  → VS.val pairSrc (pairEnv t x y) ≡ ⊤ᴮ
pair-at-checks t x y (hinx , hiny , honly) =
  cong (λ φ → VS.val φ (pairEnv t x y)) pair-shape
  ∙ VS.law-∧ pairLeftφ (pairRightφ ∧̇ pairOnlyφ) (pairEnv t x y)
  ∙ cong₂ _⊓ᴮ_ (pair-left-top t x y hinx)
      (VS.law-∧ pairRightφ pairOnlyφ (pairEnv t x y)
        ∙ cong₂ _⊓ᴮ_ (pair-right-top t x y hiny) (pair-only-top t x y honly))
  ∙ cong (⊤ᴮ ⊓ᴮ_) (⊓-⊤ ⊤ᴮ)
  ∙ ⊓-⊤ ⊤ᴮ

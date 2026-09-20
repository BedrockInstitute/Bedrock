{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile
import CardinalBridge
import Cubical.HITs.PropositionalTruncation as PT
import Cubical.Data.Empty as Empty
import K4.Algebra
import K4.Implication
import K8.FiniteVocabulary
import K9.BooleanAtomic
import K9.BooleanNameGround
import K9.NameGround
import K10.CohenValSeam
import K10.CohenBooleanCheckMem

module K10.CohenBooleanInductive
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (families : NameKernel.Families 𝒮)
  (accessible : NameKernel.Accessibility 𝒮)
  (images : NameKernel.MemberImage 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (κ w : ZFStructure.S 𝒮)
  (lem : LEM ℓ)
  (hw : ⟨ CardinalBridge.isOmega 𝒮 w ⟩)
  (paths : (x y : ZFStructure.S 𝒮)
         → (ZFStructure._≈ˢ_ 𝒮 x y) ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( var ; ⊥̇ ; ∀̇∈ ; ∃̇∈ ; _∈̇_ ; _≐_ ; _∧̇_ ; _∨̇_ )
open import FOL.Manipulation.ConstantOccurrences using ( module ZeroOccurrences )
open import Cubical.Data.Sum using ( _⊎_ ; inl ; inr )
import CardinalBridge

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open PT using ( ∣_∣₁ )

module NG = K9.NameGround 𝒮 families accessible images pow κ w
  using ( extensional ; ≈ˢ-paths )
module BAT = K9.BooleanAtomic 𝒮 families accessible images pow κ w lem
  using ( B ; module Atomic ; module IC ; module Laws ; module BK )
open K4.Algebra 𝒮 using ( Pt ; isSetPt ; _≤ᴮ_ ; ⊆ˢ-trans )
open K4.Algebra.Lattice BAT.IC.codedLattice
  using ( _⊓ᴮ_ ; _⊔ᴮ_ ; ⊤ᴮ ; ⊥ᴮ ; ⊓-lb₂ ; ⊔-ub₁ ; ⊔-ub₂ )
open K4.Implication 𝒮 NG.extensional NG.≈ˢ-paths BAT.B
  BAT.IC.codedLattice BAT.IC.codedComplement
  using ( ≤ᴮ-antisym ; ⊤-greatest ; ⊥-least ; ≤⊥→≡⊥ ; _⇒ᴮ_ ; ⇒ᴮ-curry ; ⊓-⊤ ; ⊓-comm )
module VS = K10.CohenValSeam 𝒮 families accessible images pow κ w lem paths
module BNG = K9.BooleanNameGround 𝒮 families accessible images pow κ w lem
module CM = K10.CohenBooleanCheckMem 𝒮 families accessible images pow κ w lem
module CB = CardinalBridge 𝒮
module FV = K8.FiniteVocabulary 𝒮
module ZO = ZeroOccurrences S
open BAT.Atomic using () renaming ( _∈ᴮ_ to mem ; _≈ᴮ_ to eq )

checkNm : S → VS.Nameᴮ
checkNm a = BNG.Checked.check a , BNG.Checked.check-name a

emptyEnv : VS.Envᴮ 0
emptyEnv = []

emptyBody : VS.Src 2
emptyBody = ∀̇∈ (var zero) ⊥̇

emptyClause : VS.Src 1
emptyClause = ∃̇∈ (var zero) emptyBody

support-empty : (e : S) → ⟨ FV.emptyPred e ⟩
  → (x : S) → ⟨ x ∈ˢ BNG.BSupport.support (BNG.Checked.check e) ⟩ → ⟨ ⊥ ⟩
support-empty e he x hx = PT.rec (snd ⊥)
  (λ { (b , hb , hin) → PT.rec (snd ⊥)
    (λ { (y , hy , _) → he y hy })
    (subst ⟨_⟩ (BNG.Checked.check-spec e (BNG.BK.entry x b)) hin) })
  (BNG.BSupport.entry-out (BNG.Checked.check e) x hx)

empty-mem-bot : (e : S) → ⟨ FV.emptyPred e ⟩ → (m : S)
  → mem m (BNG.Checked.check e) ≡ ⊥ᴮ
empty-mem-bot e he m = BAT.Laws.∈ᴮ-empty m (BNG.Checked.check e) (support-empty e he)

empty-body-top : (e : S) → ⟨ FV.emptyPred e ⟩
  → VS.val emptyBody (checkNm e ∷ checkNm w ∷ emptyEnv) ≡ ⊤ᴮ
empty-body-top e he = ≤ᴮ-antisym
  (⊤-greatest (VS.val emptyBody (checkNm e ∷ checkNm w ∷ emptyEnv)))
  (VS.law-∀∈-glb zero ⊥̇ (checkNm e ∷ checkNm w ∷ emptyEnv) ⊤ᴮ λ σ →
    subst (λ b → ⟨ ⊤ᴮ ≤ᴮ (mem (fst σ) (BNG.Checked.check e) ⇒ᴮ b) ⟩)
      (sym (VS.law-⊥ (σ ∷ checkNm e ∷ checkNm w ∷ emptyEnv)))
      (subst (λ m → ⟨ ⊤ᴮ ≤ᴮ (m ⇒ᴮ ⊥ᴮ) ⟩)
        (sym (empty-mem-bot e he (fst σ)))
        (⇒ᴮ-curry ⊤ᴮ ⊥ᴮ ⊥ᴮ (⊓-lb₂ ⊤ᴮ ⊥ᴮ))))

empty-clause-top : VS.val emptyClause (checkNm w ∷ emptyEnv) ≡ ⊤ᴮ
empty-clause-top = PT.rec (isSetPt BAT.B _ _) from-empty (hw .fst .fst)
  where
  from-empty : Σ[ e ∈ S ] ⟨ (e ∈ˢ w) ⊓ FV.emptyPred e ⟩
    → VS.val emptyClause (checkNm w ∷ emptyEnv) ≡ ⊤ᴮ
  from-empty (e , hin , hemp) = ≤ᴮ-antisym
    (⊤-greatest (VS.val emptyClause (checkNm w ∷ emptyEnv)))
    (subst (λ z → ⟨ z ≤ᴮ VS.val emptyClause (checkNm w ∷ emptyEnv) ⟩)
      (cong₂ _⊓ᴮ_ (CM.check-∈-top e w hin) (empty-body-top e hemp) ∙ ⊓-⊤ ⊤ᴮ)
      (VS.law-∃∈-ub zero emptyBody (checkNm w ∷ emptyEnv) (checkNm e)))

≈→≡ : {a b : S} → ⟨ a ≈ˢ b ⟩ → a ≡ b
≈→≡ {a} {b} = subst ⟨_⟩ (NG.≈ˢ-paths a b)

check-eq-top : {a b : S} → ⟨ a ≈ˢ b ⟩
  → eq (BNG.Checked.check a) (BNG.Checked.check b) ≡ ⊤ᴮ
check-eq-top {a} {b} h =
  subst (λ z → eq (BNG.Checked.check a) (BNG.Checked.check z) ≡ ⊤ᴮ)
    (≈→≡ h) (BAT.Laws.≈ᴮ-refl (BNG.Checked.check a))

succSrc : VS.Src 2
succSrc = ZO.erase CB.IsSuccOfφ refl

succMemberφ : VS.Src 2
succMemberφ = var (suc zero) ∈̇ var zero

succUpφ : VS.Src 2
succUpφ = ∀̇∈ (var (suc zero)) (var zero ∈̇ var (suc zero))

succDownφ : VS.Src 2
succDownφ = ∀̇∈ (var zero)
  ((var zero ∈̇ var (suc (suc zero))) ∨̇ (var zero ≐ var (suc (suc zero))))

succ-shape : succSrc ≡ (succMemberφ ∧̇ (succUpφ ∧̇ succDownφ))
succ-shape = refl

succEnv : S → S → VS.Envᴮ 2
succEnv y x = checkNm y ∷ checkNm x ∷ []

succ-member-top : (y x : S) → ⟨ x ∈ˢ y ⟩
  → VS.val succMemberφ (succEnv y x) ≡ ⊤ᴮ
succ-member-top y x hin =
  VS.law-∈ (suc zero) zero (succEnv y x) ∙ CM.check-∈-top x y hin

succ-up-top : (y x : S) → ⟨ ⋀ S (λ z → (z ∈ˢ x) ⇒ (z ∈ˢ y)) ⟩
  → VS.val succUpφ (succEnv y x) ≡ ⊤ᴮ
succ-up-top y x hsub = ≤ᴮ-antisym
  (⊤-greatest (VS.val succUpφ (succEnv y x)))
  (VS.law-∀∈-glb (suc zero) (var zero ∈̇ var (suc zero)) (succEnv y x) ⊤ᴮ λ σ →
    subst (λ b → ⟨ ⊤ᴮ ≤ᴮ (mem (fst σ) (BNG.Checked.check x) ⇒ᴮ b) ⟩)
      (sym (VS.law-∈ zero (suc zero) (σ ∷ succEnv y x)))
      (⇒ᴮ-curry ⊤ᴮ (mem (fst σ) (BNG.Checked.check x))
        (mem (fst σ) (BNG.Checked.check y))
        (subst (λ z → ⟨ z ≤ᴮ mem (fst σ) (BNG.Checked.check y) ⟩)
          (sym (⊓-comm ⊤ᴮ (mem (fst σ) (BNG.Checked.check x))
                ∙ ⊓-⊤ (mem (fst σ) (BNG.Checked.check x))))
          (CM.check-∈-lub x (fst σ) (mem (fst σ) (BNG.Checked.check y))
            (λ a ha → CM.check-∈-ub y a (fst σ) (hsub a ha))))))

succ-down-top : (y x : S)
  → ⟨ ⋀ S (λ z → (z ∈ˢ y) ⇒ ((z ∈ˢ x) ⊔ (z ≈ˢ x))) ⟩
  → VS.val succDownφ (succEnv y x) ≡ ⊤ᴮ
succ-down-top y x hdown = ≤ᴮ-antisym
  (⊤-greatest (VS.val succDownφ (succEnv y x)))
  (VS.law-∀∈-glb zero
    ((var zero ∈̇ var (suc (suc zero))) ∨̇ (var zero ≐ var (suc (suc zero))))
    (succEnv y x) ⊤ᴮ λ σ →
    subst (λ b → ⟨ ⊤ᴮ ≤ᴮ (mem (fst σ) (BNG.Checked.check y) ⇒ᴮ b) ⟩)
      (sym (VS.law-∨ (var zero ∈̇ var (suc (suc zero)))
        (var zero ≐ var (suc (suc zero))) (σ ∷ succEnv y x)
        ∙ cong₂ _⊔ᴮ_
          (VS.law-∈ zero (suc (suc zero)) (σ ∷ succEnv y x))
          (VS.law-≐ zero (suc (suc zero)) (σ ∷ succEnv y x))))
      (⇒ᴮ-curry ⊤ᴮ (mem (fst σ) (BNG.Checked.check y))
        (mem (fst σ) (BNG.Checked.check x)
          ⊔ᴮ eq (fst σ) (BNG.Checked.check x))
        (subst (λ z → ⟨ z ≤ᴮ (mem (fst σ) (BNG.Checked.check x)
                              ⊔ᴮ eq (fst σ) (BNG.Checked.check x)) ⟩)
          (sym (⊓-comm ⊤ᴮ (mem (fst σ) (BNG.Checked.check y))
                ∙ ⊓-⊤ (mem (fst σ) (BNG.Checked.check y))))
          (CM.check-∈-lub y (fst σ)
            (mem (fst σ) (BNG.Checked.check x)
              ⊔ᴮ eq (fst σ) (BNG.Checked.check x))
            (λ b hb → PT.rec
              (snd (eq (fst σ) (BNG.Checked.check b)
                    ≤ᴮ (mem (fst σ) (BNG.Checked.check x)
                      ⊔ᴮ eq (fst σ) (BNG.Checked.check x))))
              (choose σ b)
              (hdown b hb))))))
  where
  choose : (σ : VS.Nameᴮ) (b : S)
    → ⟨ b ∈ˢ x ⟩ ⊎ ⟨ b ≈ˢ x ⟩
    → ⟨ eq (fst σ) (BNG.Checked.check b)
        ≤ᴮ (mem (fst σ) (BNG.Checked.check x)
          ⊔ᴮ eq (fst σ) (BNG.Checked.check x)) ⟩
  choose σ b (inl hin) = ⊆ˢ-trans
    (CM.check-∈-ub x b (fst σ) hin)
    (⊔-ub₁ (mem (fst σ) (BNG.Checked.check x))
      (eq (fst σ) (BNG.Checked.check x)))
  choose σ b (inr heq) = ⊆ˢ-trans to-eq
    (⊔-ub₂ (mem (fst σ) (BNG.Checked.check x))
      (eq (fst σ) (BNG.Checked.check x)))
    where
    to-eq : ⟨ eq (fst σ) (BNG.Checked.check b)
              ≤ᴮ eq (fst σ) (BNG.Checked.check x) ⟩
    to-eq = subst (λ z → ⟨ z ≤ᴮ eq (fst σ) (BNG.Checked.check x) ⟩)
      (⊓-⊤ (eq (fst σ) (BNG.Checked.check b)))
      (subst (λ z → ⟨ (eq (fst σ) (BNG.Checked.check b) ⊓ᴮ z)
                      ≤ᴮ eq (fst σ) (BNG.Checked.check x) ⟩)
        (check-eq-top heq)
        (BAT.Laws.≈ᴮ-trans (fst σ) (BNG.Checked.check b) (BNG.Checked.check x)))

succ-at-checks : (y x : S) → ⟨ CB.isSuccOf y x ⟩
  → VS.val succSrc (succEnv y x) ≡ ⊤ᴮ
succ-at-checks y x (hin , hsub , hdown) =
  cong (λ φ → VS.val φ (succEnv y x)) succ-shape
  ∙ VS.law-∧ succMemberφ (succUpφ ∧̇ succDownφ) (succEnv y x)
  ∙ cong₂ _⊓ᴮ_ (succ-member-top y x hin)
      (VS.law-∧ succUpφ succDownφ (succEnv y x)
        ∙ cong₂ _⊓ᴮ_ (succ-up-top y x hsub) (succ-down-top y x hdown))
  ∙ cong (⊤ᴮ ⊓ᴮ_) (⊓-⊤ ⊤ᴮ)
  ∙ ⊓-⊤ ⊤ᴮ

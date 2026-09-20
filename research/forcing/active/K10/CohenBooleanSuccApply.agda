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
import K9.NameGround
import K10.CohenBooleanInductive
import K10.CohenBooleanSubst

module K10.CohenBooleanSuccApply
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
open import FOL.Syntax using ( var ; ∃̇∈ ; ∀̇∈ ; _∧̇_ ; _∈̇_ ; _≐_ ; _∨̇_ )
open import FOL.Manipulation.Renaming using ( renameFo )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open PT using ( ∣_∣₁ )
import CardinalBridge

module NG = K9.NameGround 𝒮 families accessible images pow κ w
  using ( extensional ; ≈ˢ-paths )
module BAT = K9.BooleanAtomic 𝒮 families accessible images pow κ w lem
  using ( B ; module Atomic ; module IC )
open K4.Algebra 𝒮 using ( Pt ; _≤ᴮ_ )
open K4.Algebra.Lattice BAT.IC.codedLattice using ( _⊓ᴮ_ ; _⊔ᴮ_ ; ⊤ᴮ )
open K4.Implication 𝒮 NG.extensional NG.≈ˢ-paths BAT.B
  BAT.IC.codedLattice BAT.IC.codedComplement
  using ( ≤ᴮ-antisym ; ⊤-greatest ; ⊓-⊤ ; ⊓-comm ; ⇒ᴮ-curry ; _⇒ᴮ_ )
module Ind = K10.CohenBooleanInductive 𝒮 families accessible images pow
  κ w lem hw paths
module Sub = K10.CohenBooleanSubst 𝒮 families accessible images pow κ w lem paths
module CB = CardinalBridge 𝒮

open Ind using ( checkNm ; emptyEnv ; succSrc ; succEnv ; succ-at-checks
               ; succMemberφ ; succUpφ ; succDownφ ; succ-shape
               ; emptyClause ; empty-clause-top )
open BAT.Atomic using () renaming ( _∈ᴮ_ to mem ; _≈ᴮ_ to eq )

succInner : Ind.VS.Src 3
succInner = renameFo CB.wk2 succSrc

succExists : Ind.VS.Src 2
succExists = ∃̇∈ (var (suc zero)) succInner

succClause : Ind.VS.Src 1
succClause = ∀̇∈ (var zero) succExists

indSrc : Ind.VS.Src 1
indSrc = emptyClause ∧̇ succClause

env3 : S → S → Ind.VS.Envᴮ 3
env3 m n = checkNm m ∷ checkNm n ∷ checkNm w ∷ emptyEnv

memberR : Ind.VS.Src 3
memberR = renameFo CB.wk2 succMemberφ

upR : Ind.VS.Src 3
upR = renameFo CB.wk2 succUpφ

downR : Ind.VS.Src 3
downR = renameFo CB.wk2 succDownφ

member-rename : (m n : S)
  → Ind.VS.val memberR (env3 m n) ≡ Ind.VS.val succMemberφ (succEnv m n)
member-rename m n =
  Ind.VS.law-∈ (suc zero) zero (env3 m n)
  ∙ sym (Ind.VS.law-∈ (suc zero) zero (succEnv m n))

up-body₂ : Ind.VS.Src 3
up-body₂ = var zero ∈̇ var (suc zero)

up-body₃ : Ind.VS.Src 4
up-body₃ = var zero ∈̇ var (suc zero)

up-body-rename : (σ : Ind.VS.Nameᴮ) (m n : S)
  → Ind.VS.val up-body₃ (σ ∷ env3 m n)
    ≡ Ind.VS.val up-body₂ (σ ∷ succEnv m n)
up-body-rename σ m n =
  Ind.VS.law-∈ zero (suc zero) (σ ∷ env3 m n)
  ∙ sym (Ind.VS.law-∈ zero (suc zero) (σ ∷ succEnv m n))

up-rename : (m n : S)
  → Ind.VS.val upR (env3 m n) ≡ Ind.VS.val succUpφ (succEnv m n)
up-rename m n = ≤ᴮ-antisym le ge
  where
  le : ⟨ Ind.VS.val upR (env3 m n)
         ≤ᴮ Ind.VS.val succUpφ (succEnv m n) ⟩
  le = Ind.VS.law-∀∈-glb (suc zero) up-body₂ (succEnv m n)
    (Ind.VS.val upR (env3 m n)) λ σ →
      subst (λ b → ⟨ Ind.VS.val upR (env3 m n)
                     ≤ᴮ (mem (fst σ) (fst (checkNm n)) ⇒ᴮ b) ⟩)
        (up-body-rename σ m n)
        (Ind.VS.law-∀∈-lb (suc zero) up-body₃ (env3 m n) σ)
  ge : ⟨ Ind.VS.val succUpφ (succEnv m n)
         ≤ᴮ Ind.VS.val upR (env3 m n) ⟩
  ge = Ind.VS.law-∀∈-glb (suc zero) up-body₃ (env3 m n)
    (Ind.VS.val succUpφ (succEnv m n)) λ σ →
      subst (λ b → ⟨ Ind.VS.val succUpφ (succEnv m n)
                     ≤ᴮ (mem (fst σ) (fst (checkNm n)) ⇒ᴮ b) ⟩)
        (sym (up-body-rename σ m n))
        (Ind.VS.law-∀∈-lb (suc zero) up-body₂ (succEnv m n) σ)

down-body₂ : Ind.VS.Src 3
down-body₂ =
  (var zero ∈̇ var (suc (suc zero))) ∨̇ (var zero ≐ var (suc (suc zero)))

down-body₃ : Ind.VS.Src 4
down-body₃ =
  (var zero ∈̇ var (suc (suc zero))) ∨̇ (var zero ≐ var (suc (suc zero)))

down-body-rename : (σ : Ind.VS.Nameᴮ) (m n : S)
  → Ind.VS.val down-body₃ (σ ∷ env3 m n)
    ≡ Ind.VS.val down-body₂ (σ ∷ succEnv m n)
down-body-rename σ m n =
  Ind.VS.law-∨ (var zero ∈̇ var (suc (suc zero)))
    (var zero ≐ var (suc (suc zero))) (σ ∷ env3 m n)
  ∙ cong₂ _⊔ᴮ_
      (Ind.VS.law-∈ zero (suc (suc zero)) (σ ∷ env3 m n)
        ∙ sym (Ind.VS.law-∈ zero (suc (suc zero)) (σ ∷ succEnv m n)))
      (Ind.VS.law-≐ zero (suc (suc zero)) (σ ∷ env3 m n)
        ∙ sym (Ind.VS.law-≐ zero (suc (suc zero)) (σ ∷ succEnv m n)))
  ∙ sym (Ind.VS.law-∨ (var zero ∈̇ var (suc (suc zero)))
      (var zero ≐ var (suc (suc zero))) (σ ∷ succEnv m n))

down-rename : (m n : S)
  → Ind.VS.val downR (env3 m n) ≡ Ind.VS.val succDownφ (succEnv m n)
down-rename m n = ≤ᴮ-antisym le ge
  where
  le : ⟨ Ind.VS.val downR (env3 m n)
         ≤ᴮ Ind.VS.val succDownφ (succEnv m n) ⟩
  le = Ind.VS.law-∀∈-glb zero down-body₂ (succEnv m n)
    (Ind.VS.val downR (env3 m n)) λ σ →
      subst (λ b → ⟨ Ind.VS.val downR (env3 m n)
                     ≤ᴮ (mem (fst σ) (fst (checkNm m)) ⇒ᴮ b) ⟩)
        (down-body-rename σ m n)
        (Ind.VS.law-∀∈-lb zero down-body₃ (env3 m n) σ)
  ge : ⟨ Ind.VS.val succDownφ (succEnv m n)
         ≤ᴮ Ind.VS.val downR (env3 m n) ⟩
  ge = Ind.VS.law-∀∈-glb zero down-body₃ (env3 m n)
    (Ind.VS.val succDownφ (succEnv m n)) λ σ →
      subst (λ b → ⟨ Ind.VS.val succDownφ (succEnv m n)
                     ≤ᴮ (mem (fst σ) (fst (checkNm m)) ⇒ᴮ b) ⟩)
        (sym (down-body-rename σ m n))
        (Ind.VS.law-∀∈-lb zero down-body₂ (succEnv m n) σ)

inner-shape : succInner ≡ (memberR ∧̇ (upR ∧̇ downR))
inner-shape = cong (renameFo CB.wk2) succ-shape

succ-rename : (m n : S)
  → Ind.VS.val succInner (env3 m n) ≡ Ind.VS.val succSrc (succEnv m n)
succ-rename m n =
  cong (λ φ → Ind.VS.val φ (env3 m n)) inner-shape
  ∙ Ind.VS.law-∧ memberR (upR ∧̇ downR) (env3 m n)
  ∙ cong₂ _⊓ᴮ_ (member-rename m n)
      (Ind.VS.law-∧ upR downR (env3 m n)
        ∙ cong₂ _⊓ᴮ_ (up-rename m n) (down-rename m n)
        ∙ sym (Ind.VS.law-∧ succUpφ succDownφ (succEnv m n)))
  ∙ sym (Ind.VS.law-∧ succMemberφ (succUpφ ∧̇ succDownφ) (succEnv m n))
  ∙ cong (λ φ → Ind.VS.val φ (succEnv m n)) (sym succ-shape)

succ-exists-at-check : (m n : S) → ⟨ m ∈ˢ w ⟩ → ⟨ CB.isSuccOf m n ⟩
  → Ind.VS.val succExists (checkNm n ∷ checkNm w ∷ emptyEnv) ≡ ⊤ᴮ
succ-exists-at-check m n hin hsucc = ≤ᴮ-antisym
  (⊤-greatest (Ind.VS.val succExists (checkNm n ∷ checkNm w ∷ emptyEnv)))
  (subst (λ z → ⟨ z ≤ᴮ Ind.VS.val succExists (checkNm n ∷ checkNm w ∷ emptyEnv) ⟩)
    (cong₂ _⊓ᴮ_ (Ind.CM.check-∈-top m w hin)
      (succ-rename m n ∙ succ-at-checks m n hsucc) ∙ ⊓-⊤ ⊤ᴮ)
    (Ind.VS.law-∃∈-ub (suc zero) succInner
      (checkNm n ∷ checkNm w ∷ emptyEnv) (checkNm m)))

succ-exists-subst : (n : S) (σ : Ind.VS.Nameᴮ)
  → ⟨ (eq (Ind.BNG.Checked.check n) (fst σ)
        ⊓ᴮ Ind.VS.val succExists (checkNm n ∷ checkNm w ∷ emptyEnv))
      ≤ᴮ Ind.VS.val succExists (σ ∷ checkNm w ∷ emptyEnv) ⟩
succ-exists-subst n σ =
  Sub.subst-head succExists (checkNm w ∷ emptyEnv) (checkNm n) σ

succ-exists-from-ground : (n : S) (σ : Ind.VS.Nameᴮ) → ⟨ n ∈ˢ w ⟩
  → ⟨ ⋁ S (λ m → (m ∈ˢ w) ⊓ CB.isSuccOf m n) ⟩
  → ⟨ eq (fst σ) (Ind.BNG.Checked.check n)
      ≤ᴮ Ind.VS.val succExists (σ ∷ checkNm w ∷ emptyEnv) ⟩
succ-exists-from-ground n σ hin hex = PT.rec
  (snd (eq (fst σ) (Ind.BNG.Checked.check n)
        ≤ᴮ Ind.VS.val succExists (σ ∷ checkNm w ∷ emptyEnv)))
  (λ { (m , hm , hsucc) →
    subst (λ z → ⟨ z ≤ᴮ Ind.VS.val succExists (σ ∷ checkNm w ∷ emptyEnv) ⟩)
      (⊓-⊤ (eq (Ind.BNG.Checked.check n) (fst σ))
        ∙ BAT.Atomic.≈ᴮ-sym (Ind.BNG.Checked.check n) (fst σ))
      (subst (λ z → ⟨ (eq (Ind.BNG.Checked.check n) (fst σ) ⊓ᴮ z)
                      ≤ᴮ Ind.VS.val succExists (σ ∷ checkNm w ∷ emptyEnv) ⟩)
        (succ-exists-at-check m n hm hsucc)
        (succ-exists-subst n σ)) })
  hex

opaque
  succ-clause-top : Ind.VS.val succClause (checkNm w ∷ emptyEnv) ≡ ⊤ᴮ
  succ-clause-top = ≤ᴮ-antisym
    (⊤-greatest (Ind.VS.val succClause (checkNm w ∷ emptyEnv)))
    (Ind.VS.law-∀∈-glb zero succExists (checkNm w ∷ emptyEnv) ⊤ᴮ λ σ →
      ⇒ᴮ-curry ⊤ᴮ (mem (fst σ) (Ind.BNG.Checked.check w))
        (Ind.VS.val succExists (σ ∷ checkNm w ∷ emptyEnv))
        (subst (λ z → ⟨ z ≤ᴮ Ind.VS.val succExists (σ ∷ checkNm w ∷ emptyEnv) ⟩)
          (sym (⊓-comm ⊤ᴮ (mem (fst σ) (Ind.BNG.Checked.check w))
                ∙ ⊓-⊤ (mem (fst σ) (Ind.BNG.Checked.check w))))
          (Ind.CM.check-∈-lub w (fst σ)
            (Ind.VS.val succExists (σ ∷ checkNm w ∷ emptyEnv))
            (λ n hn → succ-exists-from-ground n σ hn (hw .fst .snd n hn)))))

opaque
  inductive-at-check : Ind.VS.val indSrc (checkNm w ∷ emptyEnv) ≡ ⊤ᴮ
  inductive-at-check =
    Ind.VS.law-∧ emptyClause succClause (checkNm w ∷ emptyEnv)
    ∙ cong₂ _⊓ᴮ_ empty-clause-top succ-clause-top
    ∙ ⊓-⊤ ⊤ᴮ

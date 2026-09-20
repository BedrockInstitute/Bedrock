{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile
import CardinalBridge
import Cubical.HITs.PropositionalTruncation as PT
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Induction.WellFounded as WFI
import K4.Algebra
import K4.Implication
import K8.FiniteVocabulary
import K8.OmegaInduction
import K9.NameGround
import K10.CohenBooleanLeastSucc

module K10.CohenBooleanOmegaTop
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
open import FOL.Syntax using ( var ; ∃̇∈ ; ∀̇∈ ; _∧̇_ ; _∈̇_ ; _≐_ ; _∨̇_ ; ⊥̇
                             ; _⇒̇_ ; ∀̇_ )
open import FOL.Manipulation.Renaming using ( renameFo ; liftρ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open PT using ( ∣_∣₁ )
open WFI using ( Acc ; acc )
import CardinalBridge

module NG = K9.NameGround 𝒮 families accessible images pow κ w
  using ( extensional; hasPair; hasUnion; hasSeparation; chk-name )
module Su = K10.CohenBooleanLeastSucc 𝒮 families accessible images pow
  κ w lem hw paths using ( module Ap; contains-check-succ-clause )
module OI = K8.OmegaInduction 𝒮 NG.extensional paths NG.hasPair NG.hasUnion
  pow NG.hasSeparation κ using ( omega-predecessor )
module FV = K8.FiniteVocabulary 𝒮 using ( emptyPred )
module CB = CardinalBridge 𝒮 using ( wk1; isSuccOf )

open K4.Algebra 𝒮 using ( Pt ; _≤ᴮ_ ; ⊆ˢ-trans )
open K4.Algebra.Lattice Su.Ap.Ind.BAT.IC.codedLattice
  using ( _⊓ᴮ_ ; _⊔ᴮ_ ; ⊤ᴮ ; ⊥ᴮ ; ⊓-lb₁ ; ⊓-lb₂ ; ⊓-glb )
open K4.Implication 𝒮 Su.Ap.Ind.NG.extensional Su.Ap.Ind.NG.≈ˢ-paths
  Su.Ap.Ind.BAT.B Su.Ap.Ind.BAT.IC.codedLattice Su.Ap.Ind.BAT.IC.codedComplement
  using ( ≤ᴮ-antisym ; ⊤-greatest ; ⊓-⊤ ; ⊓-comm ; ⇒ᴮ-curry ; ⇒ᴮ-mp ; _⇒ᴮ_ )

open Su.Ap.Ind using ( checkNm ; emptyEnv ; emptyClause ; emptyBody
                     ; empty-mem-bot ; support-empty )
open Su.Ap using ( succInner ; succExists ; succClause ; indSrc
                 ; memberR ; upR ; downR ; inner-shape
                 ; up-body₃ ; down-body₃ )
open Su.Ap.Ind.BAT.Atomic using () renaming ( _∈ᴮ_ to mem ; _≈ᴮ_ to eq )

emptyBody₃ : Su.Ap.Ind.VS.Src 3
emptyBody₃ = ∀̇∈ (var zero) ⊥̇

emptyR : Su.Ap.Ind.VS.Src 2
emptyR = renameFo CB.wk1 emptyClause

emptyR-shape : emptyR ≡ ∃̇∈ (var zero) emptyBody₃
emptyR-shape = refl

empty-body-wk1 : (τ σ ρ : Su.Ap.Ind.VS.Nameᴮ)
  → Su.Ap.Ind.VS.val emptyBody₃ (τ ∷ σ ∷ ρ ∷ emptyEnv)
    ≡ Su.Ap.Ind.VS.val emptyBody (τ ∷ σ ∷ emptyEnv)
empty-body-wk1 τ σ ρ = ≤ᴮ-antisym le ge
  where
  le : ⟨ Su.Ap.Ind.VS.val emptyBody₃ (τ ∷ σ ∷ ρ ∷ emptyEnv)
         ≤ᴮ Su.Ap.Ind.VS.val emptyBody (τ ∷ σ ∷ emptyEnv) ⟩
  le = Su.Ap.Ind.VS.law-∀∈-glb zero ⊥̇ (τ ∷ σ ∷ emptyEnv)
    (Su.Ap.Ind.VS.val emptyBody₃ (τ ∷ σ ∷ ρ ∷ emptyEnv)) λ ν →
      subst (λ b → ⟨ Su.Ap.Ind.VS.val emptyBody₃ (τ ∷ σ ∷ ρ ∷ emptyEnv)
                     ≤ᴮ (mem (fst ν) (fst τ) ⇒ᴮ b) ⟩)
        (Su.Ap.Ind.VS.law-⊥ (ν ∷ τ ∷ σ ∷ ρ ∷ emptyEnv)
          ∙ sym (Su.Ap.Ind.VS.law-⊥ (ν ∷ τ ∷ σ ∷ emptyEnv)))
        (Su.Ap.Ind.VS.law-∀∈-lb zero ⊥̇ (τ ∷ σ ∷ ρ ∷ emptyEnv) ν)
  ge : ⟨ Su.Ap.Ind.VS.val emptyBody (τ ∷ σ ∷ emptyEnv)
         ≤ᴮ Su.Ap.Ind.VS.val emptyBody₃ (τ ∷ σ ∷ ρ ∷ emptyEnv) ⟩
  ge = Su.Ap.Ind.VS.law-∀∈-glb zero ⊥̇ (τ ∷ σ ∷ ρ ∷ emptyEnv)
    (Su.Ap.Ind.VS.val emptyBody (τ ∷ σ ∷ emptyEnv)) λ ν →
      subst (λ b → ⟨ Su.Ap.Ind.VS.val emptyBody (τ ∷ σ ∷ emptyEnv)
                     ≤ᴮ (mem (fst ν) (fst τ) ⇒ᴮ b) ⟩)
        (Su.Ap.Ind.VS.law-⊥ (ν ∷ τ ∷ σ ∷ emptyEnv)
          ∙ sym (Su.Ap.Ind.VS.law-⊥ (ν ∷ τ ∷ σ ∷ ρ ∷ emptyEnv)))
        (Su.Ap.Ind.VS.law-∀∈-lb zero ⊥̇ (τ ∷ σ ∷ emptyEnv) ν)

empty-wk1 : (σ ρ : Su.Ap.Ind.VS.Nameᴮ)
  → Su.Ap.Ind.VS.val emptyR (σ ∷ ρ ∷ emptyEnv)
    ≡ Su.Ap.Ind.VS.val emptyClause (σ ∷ emptyEnv)
empty-wk1 σ ρ =
  cong (λ φ → Su.Ap.Ind.VS.val φ (σ ∷ ρ ∷ emptyEnv)) emptyR-shape
  ∙ ≤ᴮ-antisym le ge
  where
  le : ⟨ Su.Ap.Ind.VS.val (∃̇∈ (var zero) emptyBody₃) (σ ∷ ρ ∷ emptyEnv)
         ≤ᴮ Su.Ap.Ind.VS.val emptyClause (σ ∷ emptyEnv) ⟩
  le = Su.Ap.Ind.VS.law-∃∈-lub zero emptyBody₃ (σ ∷ ρ ∷ emptyEnv)
    (Su.Ap.Ind.VS.val emptyClause (σ ∷ emptyEnv)) λ τ →
      subst (λ b → ⟨ (mem (fst τ) (fst σ) ⊓ᴮ b)
                     ≤ᴮ Su.Ap.Ind.VS.val emptyClause (σ ∷ emptyEnv) ⟩)
        (sym (empty-body-wk1 τ σ ρ))
        (Su.Ap.Ind.VS.law-∃∈-ub zero emptyBody (σ ∷ emptyEnv) τ)
  ge : ⟨ Su.Ap.Ind.VS.val emptyClause (σ ∷ emptyEnv)
         ≤ᴮ Su.Ap.Ind.VS.val (∃̇∈ (var zero) emptyBody₃) (σ ∷ ρ ∷ emptyEnv) ⟩
  ge = Su.Ap.Ind.VS.law-∃∈-lub zero emptyBody (σ ∷ emptyEnv)
    (Su.Ap.Ind.VS.val (∃̇∈ (var zero) emptyBody₃) (σ ∷ ρ ∷ emptyEnv)) λ τ →
      subst (λ b → ⟨ (mem (fst τ) (fst σ) ⊓ᴮ b)
                     ≤ᴮ Su.Ap.Ind.VS.val (∃̇∈ (var zero) emptyBody₃)
                          (σ ∷ ρ ∷ emptyEnv) ⟩)
        (empty-body-wk1 τ σ ρ)
        (Su.Ap.Ind.VS.law-∃∈-ub zero emptyBody₃ (σ ∷ ρ ∷ emptyEnv) τ)

succInnerR : Su.Ap.Ind.VS.Src 4
succInnerR = renameFo (liftρ (liftρ CB.wk1)) succInner

memberRR : Su.Ap.Ind.VS.Src 4
memberRR = renameFo (liftρ (liftρ CB.wk1)) memberR

upRR : Su.Ap.Ind.VS.Src 4
upRR = renameFo (liftρ (liftρ CB.wk1)) upR

downRR : Su.Ap.Ind.VS.Src 4
downRR = renameFo (liftρ (liftρ CB.wk1)) downR

up-body₄ : Su.Ap.Ind.VS.Src 5
up-body₄ = var zero ∈̇ var (suc zero)

down-body₄ : Su.Ap.Ind.VS.Src 5
down-body₄ =
  (var zero ∈̇ var (suc (suc zero))) ∨̇ (var zero ≐ var (suc (suc zero)))

member-wk1 : (υ τ σ ρ : Su.Ap.Ind.VS.Nameᴮ)
  → Su.Ap.Ind.VS.val memberRR (υ ∷ τ ∷ σ ∷ ρ ∷ emptyEnv)
    ≡ Su.Ap.Ind.VS.val memberR (υ ∷ τ ∷ σ ∷ emptyEnv)
member-wk1 υ τ σ ρ =
  Su.Ap.Ind.VS.law-∈ (suc zero) zero (υ ∷ τ ∷ σ ∷ ρ ∷ emptyEnv)
  ∙ sym (Su.Ap.Ind.VS.law-∈ (suc zero) zero (υ ∷ τ ∷ σ ∷ emptyEnv))

up-body-wk1 : (ν υ τ σ ρ : Su.Ap.Ind.VS.Nameᴮ)
  → Su.Ap.Ind.VS.val up-body₄ (ν ∷ υ ∷ τ ∷ σ ∷ ρ ∷ emptyEnv)
    ≡ Su.Ap.Ind.VS.val up-body₃ (ν ∷ υ ∷ τ ∷ σ ∷ emptyEnv)
up-body-wk1 ν υ τ σ ρ =
  Su.Ap.Ind.VS.law-∈ zero (suc zero) (ν ∷ υ ∷ τ ∷ σ ∷ ρ ∷ emptyEnv)
  ∙ sym (Su.Ap.Ind.VS.law-∈ zero (suc zero) (ν ∷ υ ∷ τ ∷ σ ∷ emptyEnv))

up-wk1 : (υ τ σ ρ : Su.Ap.Ind.VS.Nameᴮ)
  → Su.Ap.Ind.VS.val upRR (υ ∷ τ ∷ σ ∷ ρ ∷ emptyEnv)
    ≡ Su.Ap.Ind.VS.val upR (υ ∷ τ ∷ σ ∷ emptyEnv)
up-wk1 υ τ σ ρ = ≤ᴮ-antisym le ge
  where
  le : ⟨ Su.Ap.Ind.VS.val upRR (υ ∷ τ ∷ σ ∷ ρ ∷ emptyEnv)
         ≤ᴮ Su.Ap.Ind.VS.val upR (υ ∷ τ ∷ σ ∷ emptyEnv) ⟩
  le = Su.Ap.Ind.VS.law-∀∈-glb (suc zero) up-body₃ (υ ∷ τ ∷ σ ∷ emptyEnv)
    (Su.Ap.Ind.VS.val upRR (υ ∷ τ ∷ σ ∷ ρ ∷ emptyEnv)) λ ν →
      subst (λ b → ⟨ Su.Ap.Ind.VS.val upRR (υ ∷ τ ∷ σ ∷ ρ ∷ emptyEnv)
                     ≤ᴮ (mem (fst ν) (fst τ) ⇒ᴮ b) ⟩)
        (up-body-wk1 ν υ τ σ ρ)
        (Su.Ap.Ind.VS.law-∀∈-lb (suc zero) up-body₄
          (υ ∷ τ ∷ σ ∷ ρ ∷ emptyEnv) ν)
  ge : ⟨ Su.Ap.Ind.VS.val upR (υ ∷ τ ∷ σ ∷ emptyEnv)
         ≤ᴮ Su.Ap.Ind.VS.val upRR (υ ∷ τ ∷ σ ∷ ρ ∷ emptyEnv) ⟩
  ge = Su.Ap.Ind.VS.law-∀∈-glb (suc zero) up-body₄
    (υ ∷ τ ∷ σ ∷ ρ ∷ emptyEnv)
    (Su.Ap.Ind.VS.val upR (υ ∷ τ ∷ σ ∷ emptyEnv)) λ ν →
      subst (λ b → ⟨ Su.Ap.Ind.VS.val upR (υ ∷ τ ∷ σ ∷ emptyEnv)
                     ≤ᴮ (mem (fst ν) (fst τ) ⇒ᴮ b) ⟩)
        (sym (up-body-wk1 ν υ τ σ ρ))
        (Su.Ap.Ind.VS.law-∀∈-lb (suc zero) up-body₃
          (υ ∷ τ ∷ σ ∷ emptyEnv) ν)

down-body-wk1 : (ν υ τ σ ρ : Su.Ap.Ind.VS.Nameᴮ)
  → Su.Ap.Ind.VS.val down-body₄ (ν ∷ υ ∷ τ ∷ σ ∷ ρ ∷ emptyEnv)
    ≡ Su.Ap.Ind.VS.val down-body₃ (ν ∷ υ ∷ τ ∷ σ ∷ emptyEnv)
down-body-wk1 ν υ τ σ ρ =
  Su.Ap.Ind.VS.law-∨ (var zero ∈̇ var (suc (suc zero)))
    (var zero ≐ var (suc (suc zero))) (ν ∷ υ ∷ τ ∷ σ ∷ ρ ∷ emptyEnv)
  ∙ cong₂ _⊔ᴮ_
      (Su.Ap.Ind.VS.law-∈ zero (suc (suc zero))
        (ν ∷ υ ∷ τ ∷ σ ∷ ρ ∷ emptyEnv)
        ∙ sym (Su.Ap.Ind.VS.law-∈ zero (suc (suc zero))
            (ν ∷ υ ∷ τ ∷ σ ∷ emptyEnv)))
      (Su.Ap.Ind.VS.law-≐ zero (suc (suc zero))
        (ν ∷ υ ∷ τ ∷ σ ∷ ρ ∷ emptyEnv)
        ∙ sym (Su.Ap.Ind.VS.law-≐ zero (suc (suc zero))
            (ν ∷ υ ∷ τ ∷ σ ∷ emptyEnv)))
  ∙ sym (Su.Ap.Ind.VS.law-∨ (var zero ∈̇ var (suc (suc zero)))
      (var zero ≐ var (suc (suc zero))) (ν ∷ υ ∷ τ ∷ σ ∷ emptyEnv))

down-wk1 : (υ τ σ ρ : Su.Ap.Ind.VS.Nameᴮ)
  → Su.Ap.Ind.VS.val downRR (υ ∷ τ ∷ σ ∷ ρ ∷ emptyEnv)
    ≡ Su.Ap.Ind.VS.val downR (υ ∷ τ ∷ σ ∷ emptyEnv)
down-wk1 υ τ σ ρ = ≤ᴮ-antisym le ge
  where
  le : ⟨ Su.Ap.Ind.VS.val downRR (υ ∷ τ ∷ σ ∷ ρ ∷ emptyEnv)
         ≤ᴮ Su.Ap.Ind.VS.val downR (υ ∷ τ ∷ σ ∷ emptyEnv) ⟩
  le = Su.Ap.Ind.VS.law-∀∈-glb zero down-body₃ (υ ∷ τ ∷ σ ∷ emptyEnv)
    (Su.Ap.Ind.VS.val downRR (υ ∷ τ ∷ σ ∷ ρ ∷ emptyEnv)) λ ν →
      subst (λ b → ⟨ Su.Ap.Ind.VS.val downRR (υ ∷ τ ∷ σ ∷ ρ ∷ emptyEnv)
                     ≤ᴮ (mem (fst ν) (fst υ) ⇒ᴮ b) ⟩)
        (down-body-wk1 ν υ τ σ ρ)
        (Su.Ap.Ind.VS.law-∀∈-lb zero down-body₄
          (υ ∷ τ ∷ σ ∷ ρ ∷ emptyEnv) ν)
  ge : ⟨ Su.Ap.Ind.VS.val downR (υ ∷ τ ∷ σ ∷ emptyEnv)
         ≤ᴮ Su.Ap.Ind.VS.val downRR (υ ∷ τ ∷ σ ∷ ρ ∷ emptyEnv) ⟩
  ge = Su.Ap.Ind.VS.law-∀∈-glb zero down-body₄
    (υ ∷ τ ∷ σ ∷ ρ ∷ emptyEnv)
    (Su.Ap.Ind.VS.val downR (υ ∷ τ ∷ σ ∷ emptyEnv)) λ ν →
      subst (λ b → ⟨ Su.Ap.Ind.VS.val downR (υ ∷ τ ∷ σ ∷ emptyEnv)
                     ≤ᴮ (mem (fst ν) (fst υ) ⇒ᴮ b) ⟩)
        (sym (down-body-wk1 ν υ τ σ ρ))
        (Su.Ap.Ind.VS.law-∀∈-lb zero down-body₃
          (υ ∷ τ ∷ σ ∷ emptyEnv) ν)

innerR-shape : succInnerR ≡ (memberRR ∧̇ (upRR ∧̇ downRR))
innerR-shape = cong (renameFo (liftρ (liftρ CB.wk1))) inner-shape

succInner-wk1 : (υ τ σ ρ : Su.Ap.Ind.VS.Nameᴮ)
  → Su.Ap.Ind.VS.val succInnerR (υ ∷ τ ∷ σ ∷ ρ ∷ emptyEnv)
    ≡ Su.Ap.Ind.VS.val succInner (υ ∷ τ ∷ σ ∷ emptyEnv)
succInner-wk1 υ τ σ ρ =
  cong (λ φ → Su.Ap.Ind.VS.val φ (υ ∷ τ ∷ σ ∷ ρ ∷ emptyEnv)) innerR-shape
  ∙ Su.Ap.Ind.VS.law-∧ memberRR (upRR ∧̇ downRR) (υ ∷ τ ∷ σ ∷ ρ ∷ emptyEnv)
  ∙ cong₂ _⊓ᴮ_ (member-wk1 υ τ σ ρ)
      (Su.Ap.Ind.VS.law-∧ upRR downRR (υ ∷ τ ∷ σ ∷ ρ ∷ emptyEnv)
        ∙ cong₂ _⊓ᴮ_ (up-wk1 υ τ σ ρ) (down-wk1 υ τ σ ρ)
        ∙ sym (Su.Ap.Ind.VS.law-∧ upR downR (υ ∷ τ ∷ σ ∷ emptyEnv)))
  ∙ sym (Su.Ap.Ind.VS.law-∧ memberR (upR ∧̇ downR) (υ ∷ τ ∷ σ ∷ emptyEnv))
  ∙ cong (λ φ → Su.Ap.Ind.VS.val φ (υ ∷ τ ∷ σ ∷ emptyEnv)) (sym inner-shape)

succExistsR : Su.Ap.Ind.VS.Src 3
succExistsR = renameFo (liftρ CB.wk1) succExists

succExistsR-shape : succExistsR ≡ ∃̇∈ (var (suc zero)) succInnerR
succExistsR-shape = refl

succExists-wk1 : (τ σ ρ : Su.Ap.Ind.VS.Nameᴮ)
  → Su.Ap.Ind.VS.val succExistsR (τ ∷ σ ∷ ρ ∷ emptyEnv)
    ≡ Su.Ap.Ind.VS.val succExists (τ ∷ σ ∷ emptyEnv)
succExists-wk1 τ σ ρ =
  cong (λ φ → Su.Ap.Ind.VS.val φ (τ ∷ σ ∷ ρ ∷ emptyEnv)) succExistsR-shape
  ∙ ≤ᴮ-antisym le ge
  where
  le : ⟨ Su.Ap.Ind.VS.val (∃̇∈ (var (suc zero)) succInnerR)
           (τ ∷ σ ∷ ρ ∷ emptyEnv)
         ≤ᴮ Su.Ap.Ind.VS.val succExists (τ ∷ σ ∷ emptyEnv) ⟩
  le = Su.Ap.Ind.VS.law-∃∈-lub (suc zero) succInnerR (τ ∷ σ ∷ ρ ∷ emptyEnv)
    (Su.Ap.Ind.VS.val succExists (τ ∷ σ ∷ emptyEnv)) λ υ →
      subst (λ b → ⟨ (mem (fst υ) (fst σ) ⊓ᴮ b)
                     ≤ᴮ Su.Ap.Ind.VS.val succExists (τ ∷ σ ∷ emptyEnv) ⟩)
        (sym (succInner-wk1 υ τ σ ρ))
        (Su.Ap.Ind.VS.law-∃∈-ub (suc zero) succInner (τ ∷ σ ∷ emptyEnv) υ)
  ge : ⟨ Su.Ap.Ind.VS.val succExists (τ ∷ σ ∷ emptyEnv)
         ≤ᴮ Su.Ap.Ind.VS.val (∃̇∈ (var (suc zero)) succInnerR)
              (τ ∷ σ ∷ ρ ∷ emptyEnv) ⟩
  ge = Su.Ap.Ind.VS.law-∃∈-lub (suc zero) succInner (τ ∷ σ ∷ emptyEnv)
    (Su.Ap.Ind.VS.val (∃̇∈ (var (suc zero)) succInnerR)
      (τ ∷ σ ∷ ρ ∷ emptyEnv)) λ υ →
      subst (λ b → ⟨ (mem (fst υ) (fst σ) ⊓ᴮ b)
                     ≤ᴮ Su.Ap.Ind.VS.val (∃̇∈ (var (suc zero)) succInnerR)
                          (τ ∷ σ ∷ ρ ∷ emptyEnv) ⟩)
        (succInner-wk1 υ τ σ ρ)
        (Su.Ap.Ind.VS.law-∃∈-ub (suc zero) succInnerR
          (τ ∷ σ ∷ ρ ∷ emptyEnv) υ)

succR : Su.Ap.Ind.VS.Src 2
succR = renameFo CB.wk1 succClause

succR-shape : succR ≡ ∀̇∈ (var zero) succExistsR
succR-shape = refl

succ-wk1 : (σ ρ : Su.Ap.Ind.VS.Nameᴮ)
  → Su.Ap.Ind.VS.val succR (σ ∷ ρ ∷ emptyEnv)
    ≡ Su.Ap.Ind.VS.val succClause (σ ∷ emptyEnv)
succ-wk1 σ ρ =
  cong (λ φ → Su.Ap.Ind.VS.val φ (σ ∷ ρ ∷ emptyEnv)) succR-shape
  ∙ ≤ᴮ-antisym le ge
  where
  le : ⟨ Su.Ap.Ind.VS.val (∀̇∈ (var zero) succExistsR) (σ ∷ ρ ∷ emptyEnv)
         ≤ᴮ Su.Ap.Ind.VS.val succClause (σ ∷ emptyEnv) ⟩
  le = Su.Ap.Ind.VS.law-∀∈-glb zero succExists (σ ∷ emptyEnv)
    (Su.Ap.Ind.VS.val (∀̇∈ (var zero) succExistsR) (σ ∷ ρ ∷ emptyEnv)) λ τ →
      subst (λ b → ⟨ Su.Ap.Ind.VS.val (∀̇∈ (var zero) succExistsR)
                       (σ ∷ ρ ∷ emptyEnv)
                     ≤ᴮ (mem (fst τ) (fst σ) ⇒ᴮ b) ⟩)
        (succExists-wk1 τ σ ρ)
        (Su.Ap.Ind.VS.law-∀∈-lb zero succExistsR (σ ∷ ρ ∷ emptyEnv) τ)
  ge : ⟨ Su.Ap.Ind.VS.val succClause (σ ∷ emptyEnv)
         ≤ᴮ Su.Ap.Ind.VS.val (∀̇∈ (var zero) succExistsR) (σ ∷ ρ ∷ emptyEnv) ⟩
  ge = Su.Ap.Ind.VS.law-∀∈-glb zero succExistsR (σ ∷ ρ ∷ emptyEnv)
    (Su.Ap.Ind.VS.val succClause (σ ∷ emptyEnv)) λ τ →
      subst (λ b → ⟨ Su.Ap.Ind.VS.val succClause (σ ∷ emptyEnv)
                     ≤ᴮ (mem (fst τ) (fst σ) ⇒ᴮ b) ⟩)
        (sym (succExists-wk1 τ σ ρ))
        (Su.Ap.Ind.VS.law-∀∈-lb zero succExists (σ ∷ emptyEnv) τ)

indR : Su.Ap.Ind.VS.Src 2
indR = renameFo CB.wk1 indSrc

indR-shape : indR ≡ (emptyR ∧̇ succR)
indR-shape = refl

opaque
  wk1-ind : (σ ρ : Su.Ap.Ind.VS.Nameᴮ)
    → Su.Ap.Ind.VS.val (renameFo CB.wk1 indSrc) (σ ∷ ρ ∷ emptyEnv)
      ≡ Su.Ap.Ind.VS.val indSrc (σ ∷ emptyEnv)
  wk1-ind σ ρ =
    cong (λ φ → Su.Ap.Ind.VS.val φ (σ ∷ ρ ∷ emptyEnv)) indR-shape
    ∙ Su.Ap.Ind.VS.law-∧ emptyR succR (σ ∷ ρ ∷ emptyEnv)
    ∙ cong₂ _⊓ᴮ_ (empty-wk1 σ ρ) (succ-wk1 σ ρ)
    ∙ sym (Su.Ap.Ind.VS.law-∧ emptyClause succClause (σ ∷ emptyEnv))

⇒-antiˡ : (a a' b : Pt Su.Ap.Ind.BAT.B) → ⟨ a' ≤ᴮ a ⟩
  → ⟨ (a ⇒ᴮ b) ≤ᴮ (a' ⇒ᴮ b) ⟩
⇒-antiˡ a a' b h = ⇒ᴮ-curry (a ⇒ᴮ b) a' b
  (⊆ˢ-trans
    (⊓-glb (a ⇒ᴮ b) a ((a ⇒ᴮ b) ⊓ᴮ a')
      (⊓-lb₁ (a ⇒ᴮ b) a')
      (⊆ˢ-trans (⊓-lb₂ (a ⇒ᴮ b) a') h))
    (⇒ᴮ-mp a b))

weight-≤-mem : (n x : S) → ⟨ x ∈ˢ Su.Ap.Ind.BNG.BSupport.support n ⟩
  → ⟨ Su.Ap.Ind.BNG.weight n x ≤ᴮ mem x n ⟩
weight-≤-mem n x hx =
  subst (λ z → ⟨ z ≤ᴮ mem x n ⟩) (⊓-⊤ (Su.Ap.Ind.BNG.weight n x))
    (subst (λ z → ⟨ (Su.Ap.Ind.BNG.weight n x ⊓ᴮ z) ≤ᴮ mem x n ⟩)
      (Su.Ap.Ind.BAT.Laws.≈ᴮ-refl x)
      (Su.Ap.Ind.BAT.Atomic.∈ᴮ-ub x n x hx))

empty-body-le-eq : (e : S) → ⟨ FV.emptyPred e ⟩
  → (τ σ : Su.Ap.Ind.VS.Nameᴮ)
  → ⟨ Su.Ap.Ind.VS.val emptyBody (τ ∷ σ ∷ emptyEnv)
      ≤ᴮ eq (fst τ) (Su.Ap.Ind.BNG.Checked.check e) ⟩
empty-body-le-eq e he τ σ =
  Su.Ap.Ind.BAT.Atomic.≈ᴮ-glb (fst τ) (Su.Ap.Ind.BNG.Checked.check e)
    (Su.Ap.Ind.VS.val emptyBody (τ ∷ σ ∷ emptyEnv)) left right
  where
  left : (x : S) → ⟨ x ∈ˢ Su.Ap.Ind.BNG.BSupport.support (fst τ) ⟩
    → ⟨ Su.Ap.Ind.VS.val emptyBody (τ ∷ σ ∷ emptyEnv)
        ≤ᴮ (Su.Ap.Ind.BNG.weight (fst τ) x
            ⇒ᴮ mem x (Su.Ap.Ind.BNG.Checked.check e)) ⟩
  left x hx =
    subst (λ b → ⟨ Su.Ap.Ind.VS.val emptyBody (τ ∷ σ ∷ emptyEnv)
                   ≤ᴮ (Su.Ap.Ind.BNG.weight (fst τ) x ⇒ᴮ b) ⟩)
      (Su.Ap.Ind.VS.law-⊥ (ν ∷ τ ∷ σ ∷ emptyEnv)
        ∙ sym (empty-mem-bot e he x))
      (⊆ˢ-trans
        (Su.Ap.Ind.VS.law-∀∈-lb zero ⊥̇ (τ ∷ σ ∷ emptyEnv) ν)
        (⇒-antiˡ (mem x (fst τ)) (Su.Ap.Ind.BNG.weight (fst τ) x)
          (Su.Ap.Ind.VS.val ⊥̇ (ν ∷ τ ∷ σ ∷ emptyEnv))
          (weight-≤-mem (fst τ) x hx)))
    where
    ν : Su.Ap.Ind.VS.Nameᴮ
    ν = x , Su.Ap.Ind.BNG.BSupport.K.child-is-name (fst τ) (snd τ) x
      (Su.Ap.Ind.BNG.BSupport.support-out (fst τ) x hx)
  right : (y : S)
    → ⟨ y ∈ˢ Su.Ap.Ind.BNG.BSupport.support (Su.Ap.Ind.BNG.Checked.check e) ⟩
    → ⟨ Su.Ap.Ind.VS.val emptyBody (τ ∷ σ ∷ emptyEnv)
        ≤ᴮ (Su.Ap.Ind.BNG.weight (Su.Ap.Ind.BNG.Checked.check e) y
            ⇒ᴮ mem y (fst τ)) ⟩
  right y hy = Empty.rec* (support-empty e he y hy)

opaque
  contains-check-empty : (e : S) → ⟨ FV.emptyPred e ⟩
    → (σ : Su.Ap.Ind.VS.Nameᴮ)
    → ⟨ Su.Ap.Ind.VS.val emptyClause (σ ∷ emptyEnv)
        ≤ᴮ mem (Su.Ap.Ind.BNG.Checked.check e) (fst σ) ⟩
  contains-check-empty e he σ =
    Su.Ap.Ind.VS.law-∃∈-lub zero emptyBody (σ ∷ emptyEnv)
      (mem (Su.Ap.Ind.BNG.Checked.check e) (fst σ)) λ τ →
        ⊆ˢ-trans
          (⊓-glb (eq (fst τ) (Su.Ap.Ind.BNG.Checked.check e))
            (mem (fst τ) (fst σ))
            (mem (fst τ) (fst σ)
              ⊓ᴮ Su.Ap.Ind.VS.val emptyBody (τ ∷ σ ∷ emptyEnv))
            (⊆ˢ-trans (⊓-lb₂ (mem (fst τ) (fst σ))
              (Su.Ap.Ind.VS.val emptyBody (τ ∷ σ ∷ emptyEnv)))
              (empty-body-le-eq e he τ σ))
            (⊓-lb₁ (mem (fst τ) (fst σ))
              (Su.Ap.Ind.VS.val emptyBody (τ ∷ σ ∷ emptyEnv))))
          (Su.Ap.Ind.BAT.Laws.∈ᴮ-congˡ (fst τ)
            (Su.Ap.Ind.BNG.Checked.check e) (fst σ))

ind-val : (σ : Su.Ap.Ind.VS.Nameᴮ)
  → Su.Ap.Ind.VS.val indSrc (σ ∷ emptyEnv)
    ≡ (Su.Ap.Ind.VS.val emptyClause (σ ∷ emptyEnv)
        ⊓ᴮ Su.Ap.Ind.VS.val succClause (σ ∷ emptyEnv))
ind-val σ = Su.Ap.Ind.VS.law-∧ emptyClause succClause (σ ∷ emptyEnv)

contains-all-acc : (σ : Su.Ap.Ind.VS.Nameᴮ) (n : S) → ⟨ n ∈ˢ w ⟩
  → Acc _∈ᵗ_ n
  → ⟨ Su.Ap.Ind.VS.val indSrc (σ ∷ emptyEnv)
      ≤ᴮ mem (Su.Ap.Ind.BNG.Checked.check n) (fst σ) ⟩
contains-all-acc σ n hn (acc rec) = PT.rec
  (snd (Su.Ap.Ind.VS.val indSrc (σ ∷ emptyEnv)
        ≤ᴮ mem (Su.Ap.Ind.BNG.Checked.check n) (fst σ)))
  choose (OI.omega-predecessor w hw n hn)
  where
  choose : ⟨ FV.emptyPred n ⟩ Sum.⊎
           ⟨ ⋁ S (λ m → (m ∈ˢ w) ⊓ CB.isSuccOf n m) ⟩
    → ⟨ Su.Ap.Ind.VS.val indSrc (σ ∷ emptyEnv)
        ≤ᴮ mem (Su.Ap.Ind.BNG.Checked.check n) (fst σ) ⟩
  choose (Sum.inl hemp) =
    ⊆ˢ-trans
      (subst (λ z → ⟨ z ≤ᴮ Su.Ap.Ind.VS.val emptyClause (σ ∷ emptyEnv) ⟩)
        (sym (ind-val σ))
        (⊓-lb₁ (Su.Ap.Ind.VS.val emptyClause (σ ∷ emptyEnv))
          (Su.Ap.Ind.VS.val succClause (σ ∷ emptyEnv))))
      (contains-check-empty n hemp σ)
  choose (Sum.inr hex) = PT.rec
    (snd (Su.Ap.Ind.VS.val indSrc (σ ∷ emptyEnv)
          ≤ᴮ mem (Su.Ap.Ind.BNG.Checked.check n) (fst σ)))
    from-pred hex
    where
    from-pred : Σ[ m ∈ S ] ⟨ (m ∈ˢ w) ⊓ CB.isSuccOf n m ⟩
      → ⟨ Su.Ap.Ind.VS.val indSrc (σ ∷ emptyEnv)
          ≤ᴮ mem (Su.Ap.Ind.BNG.Checked.check n) (fst σ) ⟩
    from-pred (m , hm , hsucc) =
      ⊆ˢ-trans meet (Su.contains-check-succ-clause n m hsucc σ)
      where
      ih : ⟨ Su.Ap.Ind.VS.val indSrc (σ ∷ emptyEnv)
             ≤ᴮ mem (Su.Ap.Ind.BNG.Checked.check m) (fst σ) ⟩
      ih = contains-all-acc σ m hm (rec m (hsucc .fst))
      meet : ⟨ Su.Ap.Ind.VS.val indSrc (σ ∷ emptyEnv)
               ≤ᴮ (Su.Ap.Ind.VS.val succClause (σ ∷ emptyEnv)
                    ⊓ᴮ mem (Su.Ap.Ind.BNG.Checked.check m) (fst σ)) ⟩
      meet = ⊓-glb
        (Su.Ap.Ind.VS.val succClause (σ ∷ emptyEnv))
        (mem (Su.Ap.Ind.BNG.Checked.check m) (fst σ))
        (Su.Ap.Ind.VS.val indSrc (σ ∷ emptyEnv))
        (subst (λ z → ⟨ z ≤ᴮ Su.Ap.Ind.VS.val succClause (σ ∷ emptyEnv) ⟩)
          (sym (ind-val σ))
          (⊓-lb₂ (Su.Ap.Ind.VS.val emptyClause (σ ∷ emptyEnv))
            (Su.Ap.Ind.VS.val succClause (σ ∷ emptyEnv))))
        ih

opaque
  contains-all : (σ : Su.Ap.Ind.VS.Nameᴮ) (n : S) → ⟨ n ∈ˢ w ⟩
    → ⟨ Su.Ap.Ind.VS.val indSrc (σ ∷ emptyEnv)
        ≤ᴮ mem (Su.Ap.Ind.BNG.Checked.check n) (fst σ) ⟩
  contains-all σ n hn = contains-all-acc σ n hn (accessible n)

members : Su.Ap.Ind.VS.Src 2
members = ∀̇∈ (var (suc zero)) (var zero ∈̇ var (suc zero))

leastSrc : Su.Ap.Ind.VS.Src 1
leastSrc = ∀̇ ((renameFo CB.wk1 indSrc) ⇒̇ members)

omegaSrc : Su.Ap.Ind.VS.Src 1
omegaSrc = indSrc ∧̇ leastSrc

members-from-contains : (σ : Su.Ap.Ind.VS.Nameᴮ)
  → ⟨ Su.Ap.Ind.VS.val indSrc (σ ∷ emptyEnv)
      ≤ᴮ Su.Ap.Ind.VS.val members (σ ∷ checkNm w ∷ emptyEnv) ⟩
members-from-contains σ =
  Su.Ap.Ind.VS.law-∀∈-glb (suc zero) (var zero ∈̇ var (suc zero))
    (σ ∷ checkNm w ∷ emptyEnv)
    (Su.Ap.Ind.VS.val indSrc (σ ∷ emptyEnv)) λ τ →
      ⇒ᴮ-curry (Su.Ap.Ind.VS.val indSrc (σ ∷ emptyEnv))
        (mem (fst τ) (Su.Ap.Ind.BNG.Checked.check w))
        (Su.Ap.Ind.VS.val (var zero ∈̇ var (suc zero))
          (τ ∷ σ ∷ checkNm w ∷ emptyEnv))
        (subst (λ b → ⟨ (Su.Ap.Ind.VS.val indSrc (σ ∷ emptyEnv)
                          ⊓ᴮ mem (fst τ) (Su.Ap.Ind.BNG.Checked.check w))
                        ≤ᴮ b ⟩)
          (sym (Su.Ap.Ind.VS.law-∈ zero (suc zero)
            (τ ∷ σ ∷ checkNm w ∷ emptyEnv)))
          (meet τ))
  where
  meet : (τ : Su.Ap.Ind.VS.Nameᴮ)
    → ⟨ (Su.Ap.Ind.VS.val indSrc (σ ∷ emptyEnv)
          ⊓ᴮ mem (fst τ) (Su.Ap.Ind.BNG.Checked.check w))
        ≤ᴮ mem (fst τ) (fst σ) ⟩
  meet τ =
    ⊆ˢ-trans
      (⊓-glb
        (Su.Ap.Ind.VS.val indSrc (σ ∷ emptyEnv) ⇒ᴮ mem (fst τ) (fst σ))
        (Su.Ap.Ind.VS.val indSrc (σ ∷ emptyEnv))
        (Su.Ap.Ind.VS.val indSrc (σ ∷ emptyEnv)
          ⊓ᴮ mem (fst τ) (Su.Ap.Ind.BNG.Checked.check w))
        (⊆ˢ-trans
          (⊓-lb₂ (Su.Ap.Ind.VS.val indSrc (σ ∷ emptyEnv))
            (mem (fst τ) (Su.Ap.Ind.BNG.Checked.check w)))
          (Su.Ap.Ind.CM.check-∈-lub w (fst τ)
            (Su.Ap.Ind.VS.val indSrc (σ ∷ emptyEnv)
              ⇒ᴮ mem (fst τ) (fst σ))
            (λ n hn → from-n n hn)))
        (⊓-lb₁ (Su.Ap.Ind.VS.val indSrc (σ ∷ emptyEnv))
          (mem (fst τ) (Su.Ap.Ind.BNG.Checked.check w))))
      (⇒ᴮ-mp (Su.Ap.Ind.VS.val indSrc (σ ∷ emptyEnv))
        (mem (fst τ) (fst σ)))
    where
    from-n : (n : S) → ⟨ n ∈ˢ w ⟩
      → ⟨ eq (fst τ) (Su.Ap.Ind.BNG.Checked.check n)
          ≤ᴮ (Su.Ap.Ind.VS.val indSrc (σ ∷ emptyEnv)
               ⇒ᴮ mem (fst τ) (fst σ)) ⟩
    from-n n hn = ⇒ᴮ-curry
      (eq (fst τ) (Su.Ap.Ind.BNG.Checked.check n))
      (Su.Ap.Ind.VS.val indSrc (σ ∷ emptyEnv))
      (mem (fst τ) (fst σ))
      (subst (λ z → ⟨ z ≤ᴮ mem (fst τ) (fst σ) ⟩)
        (cong (Su.Ap.Ind.VS.val indSrc (σ ∷ emptyEnv) ⊓ᴮ_)
          (Su.Ap.Ind.BAT.Atomic.≈ᴮ-sym
            (Su.Ap.Ind.BNG.Checked.check n) (fst τ))
        ∙ ⊓-comm (Su.Ap.Ind.VS.val indSrc (σ ∷ emptyEnv))
            (eq (fst τ) (Su.Ap.Ind.BNG.Checked.check n)))
        (⊆ˢ-trans
          (⊓-glb
            (eq (Su.Ap.Ind.BNG.Checked.check n) (fst τ))
            (mem (Su.Ap.Ind.BNG.Checked.check n) (fst σ))
            (Su.Ap.Ind.VS.val indSrc (σ ∷ emptyEnv)
              ⊓ᴮ eq (Su.Ap.Ind.BNG.Checked.check n) (fst τ))
            (⊓-lb₂ (Su.Ap.Ind.VS.val indSrc (σ ∷ emptyEnv))
              (eq (Su.Ap.Ind.BNG.Checked.check n) (fst τ)))
            (⊆ˢ-trans
              (⊓-lb₁ (Su.Ap.Ind.VS.val indSrc (σ ∷ emptyEnv))
                (eq (Su.Ap.Ind.BNG.Checked.check n) (fst τ)))
              (contains-all σ n hn)))
          (Su.Ap.Ind.BAT.Laws.∈ᴮ-congˡ
            (Su.Ap.Ind.BNG.Checked.check n) (fst τ) (fst σ))))

least-at-check : Su.Ap.Ind.VS.val leastSrc (checkNm w ∷ emptyEnv) ≡ ⊤ᴮ
least-at-check = ≤ᴮ-antisym
  (⊤-greatest (Su.Ap.Ind.VS.val leastSrc (checkNm w ∷ emptyEnv)))
  (Su.Ap.Ind.VS.law-∀-glb
    ((renameFo CB.wk1 indSrc) ⇒̇ members)
    (checkNm w ∷ emptyEnv) ⊤ᴮ λ σ →
      subst (λ z → ⟨ ⊤ᴮ ≤ᴮ z ⟩)
        (sym (Su.Ap.Ind.VS.law-⇒ (renameFo CB.wk1 indSrc) members
          (σ ∷ checkNm w ∷ emptyEnv)))
        (subst (λ z → ⟨ ⊤ᴮ ≤ᴮ (z ⇒ᴮ Su.Ap.Ind.VS.val members
            (σ ∷ checkNm w ∷ emptyEnv)) ⟩)
          (sym (wk1-ind σ (checkNm w)))
          (⇒ᴮ-curry ⊤ᴮ
            (Su.Ap.Ind.VS.val indSrc (σ ∷ emptyEnv))
            (Su.Ap.Ind.VS.val members (σ ∷ checkNm w ∷ emptyEnv))
            (⊆ˢ-trans
              (⊓-lb₂ ⊤ᴮ (Su.Ap.Ind.VS.val indSrc (σ ∷ emptyEnv)))
              (members-from-contains σ)))))

opaque
  omega-at-check : Su.Ap.Ind.VS.val omegaSrc (checkNm w ∷ emptyEnv) ≡ ⊤ᴮ
  omega-at-check =
    Su.Ap.Ind.VS.law-∧ indSrc leastSrc (checkNm w ∷ emptyEnv)
    ∙ cong₂ _⊓ᴮ_ Su.Ap.inductive-at-check least-at-check
    ∙ ⊓-⊤ ⊤ᴮ

omegaNm : Su.Ap.Ind.VS.Nameᴮ
omegaNm =
  Su.Ap.Ind.BNG.translated-check w
  , Su.Ap.Ind.BNG.Translation.trᴮ-name
      (Su.Ap.Ind.BNG.NG.Check.chk w)
      (NG.chk-name w)

check≈omega : eq (Su.Ap.Ind.BNG.Checked.check w)
                (Su.Ap.Ind.BNG.translated-check w)
              ≡ ⊤ᴮ
check≈omega =
  Su.Ap.Ind.BAT.Atomic.≈ᴮ-sym (Su.Ap.Ind.BNG.Checked.check w)
    (Su.Ap.Ind.BNG.translated-check w)
  ∙ Su.Ap.Ind.BNG.translated-check-comparison w

opaque
  omega-at-omega : Su.Ap.Ind.VS.val omegaSrc (omegaNm ∷ emptyEnv) ≡ ⊤ᴮ
  omega-at-omega = ≤ᴮ-antisym
    (⊤-greatest (Su.Ap.Ind.VS.val omegaSrc (omegaNm ∷ emptyEnv)))
    (subst (λ z → ⟨ z ≤ᴮ Su.Ap.Ind.VS.val omegaSrc (omegaNm ∷ emptyEnv) ⟩)
      (cong₂ _⊓ᴮ_ check≈omega omega-at-check ∙ ⊓-⊤ ⊤ᴮ)
      (Su.Ap.Sub.subst₁ omegaSrc (checkNm w) omegaNm))


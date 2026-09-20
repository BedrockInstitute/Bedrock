{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile
import CardinalBridge
import K4.Algebra
import K4.Implication
import K9.BooleanAtomic
import K9.NameGround
import K10.CohenBooleanSuccApply

module K10.CohenBooleanWk1
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
open import FOL.Syntax using ( var ; ∃̇∈ ; ∀̇∈ ; _∧̇_ ; _∈̇_ ; _≐_ ; _∨̇_ ; ⊥̇ )
open import FOL.Manipulation.Renaming using ( renameFo ; liftρ )
import CardinalBridge

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

module NG = K9.NameGround 𝒮 families accessible images pow κ w
  using ( extensional ; ≈ˢ-paths )
module BAT = K9.BooleanAtomic 𝒮 families accessible images pow κ w lem
  using ( B ; module Atomic ; module IC )
open K4.Algebra 𝒮 using ( Pt ; _≤ᴮ_ )
open K4.Algebra.Lattice BAT.IC.codedLattice using ( _⊓ᴮ_ ; _⊔ᴮ_ ; ⊤ᴮ ; ⊥ᴮ )
open K4.Implication 𝒮 NG.extensional NG.≈ˢ-paths BAT.B
  BAT.IC.codedLattice BAT.IC.codedComplement
  using ( ≤ᴮ-antisym ; ⊤-greatest ; ⊓-⊤ ; ⇒ᴮ-curry ; _⇒ᴮ_ )
module Ap = K10.CohenBooleanSuccApply 𝒮 families accessible images pow
  κ w lem hw paths
module CB = CardinalBridge 𝒮

open Ap.Ind using ( checkNm ; emptyEnv ; emptyBody ; emptyClause )
open Ap using ( succInner ; succExists ; succClause ; indSrc
              ; memberR ; upR ; downR ; inner-shape
              ; up-body₂ ; up-body₃ ; down-body₂ ; down-body₃ )
open BAT.Atomic using () renaming ( _∈ᴮ_ to mem ; _≈ᴮ_ to eq )

emptyBody₃ : Ap.Ind.VS.Src 3
emptyBody₃ = ∀̇∈ (var zero) ⊥̇

emptyR : Ap.Ind.VS.Src 2
emptyR = renameFo CB.wk1 emptyClause

emptyR-shape : emptyR ≡ ∃̇∈ (var zero) emptyBody₃
emptyR-shape = refl

empty-body-wk1 : (τ σ ρ : Ap.Ind.VS.Nameᴮ)
  → Ap.Ind.VS.val emptyBody₃ (τ ∷ σ ∷ ρ ∷ emptyEnv)
    ≡ Ap.Ind.VS.val emptyBody (τ ∷ σ ∷ emptyEnv)
empty-body-wk1 τ σ ρ = ≤ᴮ-antisym le ge
  where
  le : ⟨ Ap.Ind.VS.val emptyBody₃ (τ ∷ σ ∷ ρ ∷ emptyEnv)
         ≤ᴮ Ap.Ind.VS.val emptyBody (τ ∷ σ ∷ emptyEnv) ⟩
  le = Ap.Ind.VS.law-∀∈-glb zero ⊥̇ (τ ∷ σ ∷ emptyEnv)
    (Ap.Ind.VS.val emptyBody₃ (τ ∷ σ ∷ ρ ∷ emptyEnv)) λ ν →
      subst (λ b → ⟨ Ap.Ind.VS.val emptyBody₃ (τ ∷ σ ∷ ρ ∷ emptyEnv)
                     ≤ᴮ (mem (fst ν) (fst τ) ⇒ᴮ b) ⟩)
        (Ap.Ind.VS.law-⊥ (ν ∷ τ ∷ σ ∷ ρ ∷ emptyEnv)
          ∙ sym (Ap.Ind.VS.law-⊥ (ν ∷ τ ∷ σ ∷ emptyEnv)))
        (Ap.Ind.VS.law-∀∈-lb zero ⊥̇ (τ ∷ σ ∷ ρ ∷ emptyEnv) ν)
  ge : ⟨ Ap.Ind.VS.val emptyBody (τ ∷ σ ∷ emptyEnv)
         ≤ᴮ Ap.Ind.VS.val emptyBody₃ (τ ∷ σ ∷ ρ ∷ emptyEnv) ⟩
  ge = Ap.Ind.VS.law-∀∈-glb zero ⊥̇ (τ ∷ σ ∷ ρ ∷ emptyEnv)
    (Ap.Ind.VS.val emptyBody (τ ∷ σ ∷ emptyEnv)) λ ν →
      subst (λ b → ⟨ Ap.Ind.VS.val emptyBody (τ ∷ σ ∷ emptyEnv)
                     ≤ᴮ (mem (fst ν) (fst τ) ⇒ᴮ b) ⟩)
        (Ap.Ind.VS.law-⊥ (ν ∷ τ ∷ σ ∷ emptyEnv)
          ∙ sym (Ap.Ind.VS.law-⊥ (ν ∷ τ ∷ σ ∷ ρ ∷ emptyEnv)))
        (Ap.Ind.VS.law-∀∈-lb zero ⊥̇ (τ ∷ σ ∷ emptyEnv) ν)

empty-wk1 : (σ ρ : Ap.Ind.VS.Nameᴮ)
  → Ap.Ind.VS.val emptyR (σ ∷ ρ ∷ emptyEnv)
    ≡ Ap.Ind.VS.val emptyClause (σ ∷ emptyEnv)
empty-wk1 σ ρ =
  cong (λ φ → Ap.Ind.VS.val φ (σ ∷ ρ ∷ emptyEnv)) emptyR-shape
  ∙ ≤ᴮ-antisym le ge
  where
  le : ⟨ Ap.Ind.VS.val (∃̇∈ (var zero) emptyBody₃) (σ ∷ ρ ∷ emptyEnv)
         ≤ᴮ Ap.Ind.VS.val emptyClause (σ ∷ emptyEnv) ⟩
  le = Ap.Ind.VS.law-∃∈-lub zero emptyBody₃ (σ ∷ ρ ∷ emptyEnv)
    (Ap.Ind.VS.val emptyClause (σ ∷ emptyEnv)) λ τ →
      subst (λ b → ⟨ (mem (fst τ) (fst σ) ⊓ᴮ b)
                     ≤ᴮ Ap.Ind.VS.val emptyClause (σ ∷ emptyEnv) ⟩)
        (sym (empty-body-wk1 τ σ ρ))
        (Ap.Ind.VS.law-∃∈-ub zero emptyBody (σ ∷ emptyEnv) τ)
  ge : ⟨ Ap.Ind.VS.val emptyClause (σ ∷ emptyEnv)
         ≤ᴮ Ap.Ind.VS.val (∃̇∈ (var zero) emptyBody₃) (σ ∷ ρ ∷ emptyEnv) ⟩
  ge = Ap.Ind.VS.law-∃∈-lub zero emptyBody (σ ∷ emptyEnv)
    (Ap.Ind.VS.val (∃̇∈ (var zero) emptyBody₃) (σ ∷ ρ ∷ emptyEnv)) λ τ →
      subst (λ b → ⟨ (mem (fst τ) (fst σ) ⊓ᴮ b)
                     ≤ᴮ Ap.Ind.VS.val (∃̇∈ (var zero) emptyBody₃)
                          (σ ∷ ρ ∷ emptyEnv) ⟩)
        (empty-body-wk1 τ σ ρ)
        (Ap.Ind.VS.law-∃∈-ub zero emptyBody₃ (σ ∷ ρ ∷ emptyEnv) τ)

succInnerR : Ap.Ind.VS.Src 4
succInnerR = renameFo (liftρ (liftρ CB.wk1)) succInner

memberRR : Ap.Ind.VS.Src 4
memberRR = renameFo (liftρ (liftρ CB.wk1)) memberR

upRR : Ap.Ind.VS.Src 4
upRR = renameFo (liftρ (liftρ CB.wk1)) upR

downRR : Ap.Ind.VS.Src 4
downRR = renameFo (liftρ (liftρ CB.wk1)) downR

up-body₄ : Ap.Ind.VS.Src 5
up-body₄ = var zero ∈̇ var (suc zero)

down-body₄ : Ap.Ind.VS.Src 5
down-body₄ =
  (var zero ∈̇ var (suc (suc zero))) ∨̇ (var zero ≐ var (suc (suc zero)))

member-wk1 : (υ τ σ ρ : Ap.Ind.VS.Nameᴮ)
  → Ap.Ind.VS.val memberRR (υ ∷ τ ∷ σ ∷ ρ ∷ emptyEnv)
    ≡ Ap.Ind.VS.val memberR (υ ∷ τ ∷ σ ∷ emptyEnv)
member-wk1 υ τ σ ρ =
  Ap.Ind.VS.law-∈ (suc zero) zero (υ ∷ τ ∷ σ ∷ ρ ∷ emptyEnv)
  ∙ sym (Ap.Ind.VS.law-∈ (suc zero) zero (υ ∷ τ ∷ σ ∷ emptyEnv))

up-body-wk1 : (ν υ τ σ ρ : Ap.Ind.VS.Nameᴮ)
  → Ap.Ind.VS.val up-body₄ (ν ∷ υ ∷ τ ∷ σ ∷ ρ ∷ emptyEnv)
    ≡ Ap.Ind.VS.val up-body₃ (ν ∷ υ ∷ τ ∷ σ ∷ emptyEnv)
up-body-wk1 ν υ τ σ ρ =
  Ap.Ind.VS.law-∈ zero (suc zero) (ν ∷ υ ∷ τ ∷ σ ∷ ρ ∷ emptyEnv)
  ∙ sym (Ap.Ind.VS.law-∈ zero (suc zero) (ν ∷ υ ∷ τ ∷ σ ∷ emptyEnv))

up-wk1 : (υ τ σ ρ : Ap.Ind.VS.Nameᴮ)
  → Ap.Ind.VS.val upRR (υ ∷ τ ∷ σ ∷ ρ ∷ emptyEnv)
    ≡ Ap.Ind.VS.val upR (υ ∷ τ ∷ σ ∷ emptyEnv)
up-wk1 υ τ σ ρ = ≤ᴮ-antisym le ge
  where
  le : ⟨ Ap.Ind.VS.val upRR (υ ∷ τ ∷ σ ∷ ρ ∷ emptyEnv)
         ≤ᴮ Ap.Ind.VS.val upR (υ ∷ τ ∷ σ ∷ emptyEnv) ⟩
  le = Ap.Ind.VS.law-∀∈-glb (suc zero) up-body₃ (υ ∷ τ ∷ σ ∷ emptyEnv)
    (Ap.Ind.VS.val upRR (υ ∷ τ ∷ σ ∷ ρ ∷ emptyEnv)) λ ν →
      subst (λ b → ⟨ Ap.Ind.VS.val upRR (υ ∷ τ ∷ σ ∷ ρ ∷ emptyEnv)
                     ≤ᴮ (mem (fst ν) (fst τ) ⇒ᴮ b) ⟩)
        (up-body-wk1 ν υ τ σ ρ)
        (Ap.Ind.VS.law-∀∈-lb (suc zero) up-body₄
          (υ ∷ τ ∷ σ ∷ ρ ∷ emptyEnv) ν)
  ge : ⟨ Ap.Ind.VS.val upR (υ ∷ τ ∷ σ ∷ emptyEnv)
         ≤ᴮ Ap.Ind.VS.val upRR (υ ∷ τ ∷ σ ∷ ρ ∷ emptyEnv) ⟩
  ge = Ap.Ind.VS.law-∀∈-glb (suc zero) up-body₄
    (υ ∷ τ ∷ σ ∷ ρ ∷ emptyEnv)
    (Ap.Ind.VS.val upR (υ ∷ τ ∷ σ ∷ emptyEnv)) λ ν →
      subst (λ b → ⟨ Ap.Ind.VS.val upR (υ ∷ τ ∷ σ ∷ emptyEnv)
                     ≤ᴮ (mem (fst ν) (fst τ) ⇒ᴮ b) ⟩)
        (sym (up-body-wk1 ν υ τ σ ρ))
        (Ap.Ind.VS.law-∀∈-lb (suc zero) up-body₃
          (υ ∷ τ ∷ σ ∷ emptyEnv) ν)

down-body-wk1 : (ν υ τ σ ρ : Ap.Ind.VS.Nameᴮ)
  → Ap.Ind.VS.val down-body₄ (ν ∷ υ ∷ τ ∷ σ ∷ ρ ∷ emptyEnv)
    ≡ Ap.Ind.VS.val down-body₃ (ν ∷ υ ∷ τ ∷ σ ∷ emptyEnv)
down-body-wk1 ν υ τ σ ρ =
  Ap.Ind.VS.law-∨ (var zero ∈̇ var (suc (suc zero)))
    (var zero ≐ var (suc (suc zero))) (ν ∷ υ ∷ τ ∷ σ ∷ ρ ∷ emptyEnv)
  ∙ cong₂ _⊔ᴮ_
      (Ap.Ind.VS.law-∈ zero (suc (suc zero))
        (ν ∷ υ ∷ τ ∷ σ ∷ ρ ∷ emptyEnv)
        ∙ sym (Ap.Ind.VS.law-∈ zero (suc (suc zero))
            (ν ∷ υ ∷ τ ∷ σ ∷ emptyEnv)))
      (Ap.Ind.VS.law-≐ zero (suc (suc zero))
        (ν ∷ υ ∷ τ ∷ σ ∷ ρ ∷ emptyEnv)
        ∙ sym (Ap.Ind.VS.law-≐ zero (suc (suc zero))
            (ν ∷ υ ∷ τ ∷ σ ∷ emptyEnv)))
  ∙ sym (Ap.Ind.VS.law-∨ (var zero ∈̇ var (suc (suc zero)))
      (var zero ≐ var (suc (suc zero))) (ν ∷ υ ∷ τ ∷ σ ∷ emptyEnv))

down-wk1 : (υ τ σ ρ : Ap.Ind.VS.Nameᴮ)
  → Ap.Ind.VS.val downRR (υ ∷ τ ∷ σ ∷ ρ ∷ emptyEnv)
    ≡ Ap.Ind.VS.val downR (υ ∷ τ ∷ σ ∷ emptyEnv)
down-wk1 υ τ σ ρ = ≤ᴮ-antisym le ge
  where
  le : ⟨ Ap.Ind.VS.val downRR (υ ∷ τ ∷ σ ∷ ρ ∷ emptyEnv)
         ≤ᴮ Ap.Ind.VS.val downR (υ ∷ τ ∷ σ ∷ emptyEnv) ⟩
  le = Ap.Ind.VS.law-∀∈-glb zero down-body₃ (υ ∷ τ ∷ σ ∷ emptyEnv)
    (Ap.Ind.VS.val downRR (υ ∷ τ ∷ σ ∷ ρ ∷ emptyEnv)) λ ν →
      subst (λ b → ⟨ Ap.Ind.VS.val downRR (υ ∷ τ ∷ σ ∷ ρ ∷ emptyEnv)
                     ≤ᴮ (mem (fst ν) (fst υ) ⇒ᴮ b) ⟩)
        (down-body-wk1 ν υ τ σ ρ)
        (Ap.Ind.VS.law-∀∈-lb zero down-body₄
          (υ ∷ τ ∷ σ ∷ ρ ∷ emptyEnv) ν)
  ge : ⟨ Ap.Ind.VS.val downR (υ ∷ τ ∷ σ ∷ emptyEnv)
         ≤ᴮ Ap.Ind.VS.val downRR (υ ∷ τ ∷ σ ∷ ρ ∷ emptyEnv) ⟩
  ge = Ap.Ind.VS.law-∀∈-glb zero down-body₄
    (υ ∷ τ ∷ σ ∷ ρ ∷ emptyEnv)
    (Ap.Ind.VS.val downR (υ ∷ τ ∷ σ ∷ emptyEnv)) λ ν →
      subst (λ b → ⟨ Ap.Ind.VS.val downR (υ ∷ τ ∷ σ ∷ emptyEnv)
                     ≤ᴮ (mem (fst ν) (fst υ) ⇒ᴮ b) ⟩)
        (sym (down-body-wk1 ν υ τ σ ρ))
        (Ap.Ind.VS.law-∀∈-lb zero down-body₃
          (υ ∷ τ ∷ σ ∷ emptyEnv) ν)

innerR-shape : succInnerR ≡ (memberRR ∧̇ (upRR ∧̇ downRR))
innerR-shape = cong (renameFo (liftρ (liftρ CB.wk1))) inner-shape

succInner-wk1 : (υ τ σ ρ : Ap.Ind.VS.Nameᴮ)
  → Ap.Ind.VS.val succInnerR (υ ∷ τ ∷ σ ∷ ρ ∷ emptyEnv)
    ≡ Ap.Ind.VS.val succInner (υ ∷ τ ∷ σ ∷ emptyEnv)
succInner-wk1 υ τ σ ρ =
  cong (λ φ → Ap.Ind.VS.val φ (υ ∷ τ ∷ σ ∷ ρ ∷ emptyEnv)) innerR-shape
  ∙ Ap.Ind.VS.law-∧ memberRR (upRR ∧̇ downRR) (υ ∷ τ ∷ σ ∷ ρ ∷ emptyEnv)
  ∙ cong₂ _⊓ᴮ_ (member-wk1 υ τ σ ρ)
      (Ap.Ind.VS.law-∧ upRR downRR (υ ∷ τ ∷ σ ∷ ρ ∷ emptyEnv)
        ∙ cong₂ _⊓ᴮ_ (up-wk1 υ τ σ ρ) (down-wk1 υ τ σ ρ)
        ∙ sym (Ap.Ind.VS.law-∧ upR downR (υ ∷ τ ∷ σ ∷ emptyEnv)))
  ∙ sym (Ap.Ind.VS.law-∧ memberR (upR ∧̇ downR) (υ ∷ τ ∷ σ ∷ emptyEnv))
  ∙ cong (λ φ → Ap.Ind.VS.val φ (υ ∷ τ ∷ σ ∷ emptyEnv)) (sym inner-shape)

succExistsR : Ap.Ind.VS.Src 3
succExistsR = renameFo (liftρ CB.wk1) succExists

succExistsR-shape : succExistsR ≡ ∃̇∈ (var (suc zero)) succInnerR
succExistsR-shape = refl

succExists-wk1 : (τ σ ρ : Ap.Ind.VS.Nameᴮ)
  → Ap.Ind.VS.val succExistsR (τ ∷ σ ∷ ρ ∷ emptyEnv)
    ≡ Ap.Ind.VS.val succExists (τ ∷ σ ∷ emptyEnv)
succExists-wk1 τ σ ρ =
  cong (λ φ → Ap.Ind.VS.val φ (τ ∷ σ ∷ ρ ∷ emptyEnv)) succExistsR-shape
  ∙ ≤ᴮ-antisym le ge
  where
  le : ⟨ Ap.Ind.VS.val (∃̇∈ (var (suc zero)) succInnerR)
           (τ ∷ σ ∷ ρ ∷ emptyEnv)
         ≤ᴮ Ap.Ind.VS.val succExists (τ ∷ σ ∷ emptyEnv) ⟩
  le = Ap.Ind.VS.law-∃∈-lub (suc zero) succInnerR (τ ∷ σ ∷ ρ ∷ emptyEnv)
    (Ap.Ind.VS.val succExists (τ ∷ σ ∷ emptyEnv)) λ υ →
      subst (λ b → ⟨ (mem (fst υ) (fst σ) ⊓ᴮ b)
                     ≤ᴮ Ap.Ind.VS.val succExists (τ ∷ σ ∷ emptyEnv) ⟩)
        (sym (succInner-wk1 υ τ σ ρ))
        (Ap.Ind.VS.law-∃∈-ub (suc zero) succInner (τ ∷ σ ∷ emptyEnv) υ)
  ge : ⟨ Ap.Ind.VS.val succExists (τ ∷ σ ∷ emptyEnv)
         ≤ᴮ Ap.Ind.VS.val (∃̇∈ (var (suc zero)) succInnerR)
              (τ ∷ σ ∷ ρ ∷ emptyEnv) ⟩
  ge = Ap.Ind.VS.law-∃∈-lub (suc zero) succInner (τ ∷ σ ∷ emptyEnv)
    (Ap.Ind.VS.val (∃̇∈ (var (suc zero)) succInnerR)
      (τ ∷ σ ∷ ρ ∷ emptyEnv)) λ υ →
      subst (λ b → ⟨ (mem (fst υ) (fst σ) ⊓ᴮ b)
                     ≤ᴮ Ap.Ind.VS.val (∃̇∈ (var (suc zero)) succInnerR)
                          (τ ∷ σ ∷ ρ ∷ emptyEnv) ⟩)
        (succInner-wk1 υ τ σ ρ)
        (Ap.Ind.VS.law-∃∈-ub (suc zero) succInnerR
          (τ ∷ σ ∷ ρ ∷ emptyEnv) υ)

succR : Ap.Ind.VS.Src 2
succR = renameFo CB.wk1 succClause

succR-shape : succR ≡ ∀̇∈ (var zero) succExistsR
succR-shape = refl

succ-wk1 : (σ ρ : Ap.Ind.VS.Nameᴮ)
  → Ap.Ind.VS.val succR (σ ∷ ρ ∷ emptyEnv)
    ≡ Ap.Ind.VS.val succClause (σ ∷ emptyEnv)
succ-wk1 σ ρ =
  cong (λ φ → Ap.Ind.VS.val φ (σ ∷ ρ ∷ emptyEnv)) succR-shape
  ∙ ≤ᴮ-antisym le ge
  where
  le : ⟨ Ap.Ind.VS.val (∀̇∈ (var zero) succExistsR) (σ ∷ ρ ∷ emptyEnv)
         ≤ᴮ Ap.Ind.VS.val succClause (σ ∷ emptyEnv) ⟩
  le = Ap.Ind.VS.law-∀∈-glb zero succExists (σ ∷ emptyEnv)
    (Ap.Ind.VS.val (∀̇∈ (var zero) succExistsR) (σ ∷ ρ ∷ emptyEnv)) λ τ →
      subst (λ b → ⟨ Ap.Ind.VS.val (∀̇∈ (var zero) succExistsR)
                       (σ ∷ ρ ∷ emptyEnv)
                     ≤ᴮ (mem (fst τ) (fst σ) ⇒ᴮ b) ⟩)
        (succExists-wk1 τ σ ρ)
        (Ap.Ind.VS.law-∀∈-lb zero succExistsR (σ ∷ ρ ∷ emptyEnv) τ)
  ge : ⟨ Ap.Ind.VS.val succClause (σ ∷ emptyEnv)
         ≤ᴮ Ap.Ind.VS.val (∀̇∈ (var zero) succExistsR) (σ ∷ ρ ∷ emptyEnv) ⟩
  ge = Ap.Ind.VS.law-∀∈-glb zero succExistsR (σ ∷ ρ ∷ emptyEnv)
    (Ap.Ind.VS.val succClause (σ ∷ emptyEnv)) λ τ →
      subst (λ b → ⟨ Ap.Ind.VS.val succClause (σ ∷ emptyEnv)
                     ≤ᴮ (mem (fst τ) (fst σ) ⇒ᴮ b) ⟩)
        (sym (succExists-wk1 τ σ ρ))
        (Ap.Ind.VS.law-∀∈-lb zero succExists (σ ∷ emptyEnv) τ)

indR : Ap.Ind.VS.Src 2
indR = renameFo CB.wk1 indSrc

indR-shape : indR ≡ (emptyR ∧̇ succR)
indR-shape = refl

opaque
  wk1-ind : (σ ρ : Ap.Ind.VS.Nameᴮ)
    → Ap.Ind.VS.val (renameFo CB.wk1 indSrc) (σ ∷ ρ ∷ emptyEnv)
      ≡ Ap.Ind.VS.val indSrc (σ ∷ emptyEnv)
  wk1-ind σ ρ =
    cong (λ φ → Ap.Ind.VS.val φ (σ ∷ ρ ∷ emptyEnv)) indR-shape
    ∙ Ap.Ind.VS.law-∧ emptyR succR (σ ∷ ρ ∷ emptyEnv)
    ∙ cong₂ _⊓ᴮ_ (empty-wk1 σ ρ) (succ-wk1 σ ρ)
    ∙ sym (Ap.Ind.VS.law-∧ emptyClause succClause (σ ∷ emptyEnv))

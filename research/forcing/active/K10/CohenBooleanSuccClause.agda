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
import K10.CohenBooleanSubst

module K10.CohenBooleanSuccClause
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
open import FOL.Syntax using ( var ; ∃̇∈ ; ∀̇∈ ; _∧̇_ ; ⊥̇ )
open import FOL.Manipulation.ConstantOccurrences using ( module ZeroOccurrences )
open import FOL.Manipulation.Renaming using ( renameFo )
import CardinalBridge

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open PT using ( ∣_∣₁ )

module NG = K9.NameGround 𝒮 families accessible images pow κ w
  using ( extensional ; ≈ˢ-paths )
module BAT = K9.BooleanAtomic 𝒮 families accessible images pow κ w lem
  using ( B ; module Atomic ; module IC )
open K4.Algebra 𝒮 using ( Pt ; _≤ᴮ_ )
open K4.Algebra.Lattice BAT.IC.codedLattice using ( _⊓ᴮ_ ; ⊤ᴮ )
open K4.Implication 𝒮 NG.extensional NG.≈ˢ-paths BAT.B
  BAT.IC.codedLattice BAT.IC.codedComplement
  using ( ≤ᴮ-antisym ; ⊤-greatest ; ⊓-⊤ ; ⊓-comm ; ⇒ᴮ-curry )
module VS = K10.CohenValSeam 𝒮 families accessible images pow κ w lem paths
module BNG = K9.BooleanNameGround 𝒮 families accessible images pow κ w lem
module CM = K10.CohenBooleanCheckMem 𝒮 families accessible images pow κ w lem
module Sub = K10.CohenBooleanSubst 𝒮 families accessible images pow κ w lem paths
module CB = CardinalBridge 𝒮
module ZO = ZeroOccurrences S

open BAT.Atomic using () renaming ( _∈ᴮ_ to mem ; _≈ᴮ_ to eq )

checkNm : S → VS.Nameᴮ
checkNm a = BNG.Checked.check a , BNG.Checked.check-name a

emptyEnv : VS.Envᴮ 0
emptyEnv = []

succSrc : VS.Src 2
succSrc = ZO.erase CB.IsSuccOfφ refl

succInner : VS.Src 3
succInner = renameFo CB.wk2 succSrc

succExists : VS.Src 2
succExists = ∃̇∈ (var (suc zero)) succInner

succClause : VS.Src 1
succClause = ∀̇∈ (var zero) succExists

emptyBody : VS.Src 2
emptyBody = ∀̇∈ (var zero) ⊥̇

emptyClause : VS.Src 1
emptyClause = ∃̇∈ (var zero) emptyBody

indSrc : VS.Src 1
indSrc = emptyClause ∧̇ succClause

succ-exists-subst : (n : S) (σ : VS.Nameᴮ)
  → ⟨ (eq (BNG.Checked.check n) (fst σ)
        ⊓ᴮ VS.val succExists (checkNm n ∷ checkNm w ∷ emptyEnv))
      ≤ᴮ VS.val succExists (σ ∷ checkNm w ∷ emptyEnv) ⟩
succ-exists-subst n σ =
  Sub.subst-head succExists (checkNm w ∷ emptyEnv) (checkNm n) σ

module FromExists
  (succ-exists-at-check : (m n : S) → ⟨ m ∈ˢ w ⟩ → ⟨ CB.isSuccOf m n ⟩
    → VS.val succExists (checkNm n ∷ checkNm w ∷ emptyEnv) ≡ ⊤ᴮ)
  where

  succ-exists-from-ground : (n : S) (σ : VS.Nameᴮ) → ⟨ n ∈ˢ w ⟩
    → ⟨ ⋁ S (λ m → (m ∈ˢ w) ⊓ CB.isSuccOf m n) ⟩
    → ⟨ eq (fst σ) (BNG.Checked.check n)
        ≤ᴮ VS.val succExists (σ ∷ checkNm w ∷ emptyEnv) ⟩
  succ-exists-from-ground n σ hin hex = PT.rec
    (snd (eq (fst σ) (BNG.Checked.check n)
          ≤ᴮ VS.val succExists (σ ∷ checkNm w ∷ emptyEnv)))
    (λ { (m , hm , hsucc) →
      subst (λ z → ⟨ z ≤ᴮ VS.val succExists (σ ∷ checkNm w ∷ emptyEnv) ⟩)
        (⊓-⊤ (eq (BNG.Checked.check n) (fst σ))
          ∙ BAT.Atomic.≈ᴮ-sym (BNG.Checked.check n) (fst σ))
        (subst (λ z → ⟨ (eq (BNG.Checked.check n) (fst σ) ⊓ᴮ z)
                        ≤ᴮ VS.val succExists (σ ∷ checkNm w ∷ emptyEnv) ⟩)
          (succ-exists-at-check m n hm hsucc)
          (succ-exists-subst n σ)) })
    hex

  opaque
    succ-clause-top : VS.val succClause (checkNm w ∷ emptyEnv) ≡ ⊤ᴮ
    succ-clause-top = ≤ᴮ-antisym
      (⊤-greatest (VS.val succClause (checkNm w ∷ emptyEnv)))
      (VS.law-∀∈-glb zero succExists (checkNm w ∷ emptyEnv) ⊤ᴮ λ σ →
        ⇒ᴮ-curry ⊤ᴮ (mem (fst σ) (BNG.Checked.check w))
          (VS.val succExists (σ ∷ checkNm w ∷ emptyEnv))
          (subst (λ z → ⟨ z ≤ᴮ VS.val succExists (σ ∷ checkNm w ∷ emptyEnv) ⟩)
            (sym (⊓-comm ⊤ᴮ (mem (fst σ) (BNG.Checked.check w))
                  ∙ ⊓-⊤ (mem (fst σ) (BNG.Checked.check w))))
            (CM.check-∈-lub w (fst σ)
              (VS.val succExists (σ ∷ checkNm w ∷ emptyEnv))
              (λ n hn → succ-exists-from-ground n σ hn (hw .fst .snd n hn)))))

  module FromEmpty
    (empty-clause-top : VS.val emptyClause (checkNm w ∷ emptyEnv) ≡ ⊤ᴮ)
    where

    inductive-at-check : VS.val indSrc (checkNm w ∷ emptyEnv) ≡ ⊤ᴮ
    inductive-at-check =
      VS.law-∧ emptyClause succClause (checkNm w ∷ emptyEnv)
      ∙ cong₂ _⊓ᴮ_ empty-clause-top succ-clause-top
      ∙ ⊓-⊤ ⊤ᴮ

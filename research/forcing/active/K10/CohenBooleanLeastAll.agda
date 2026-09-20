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
import Cubical.Induction.WellFounded as WFI
import K4.Algebra
import K4.Implication
import K8.FiniteVocabulary
import K8.OmegaInduction
import K9.NameGround
import K10.CohenBooleanLeastSucc

module K10.CohenBooleanLeastAll
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

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open PT using ( ∣_∣₁ )
open WFI using ( Acc ; acc )
import CardinalBridge

module NG = K9.NameGround 𝒮 families accessible images pow κ w
module Su = K10.CohenBooleanLeastSucc 𝒮 families accessible images pow
  κ w lem hw paths
module OI = K8.OmegaInduction 𝒮 NG.extensional paths NG.hasPair NG.hasUnion
  pow NG.hasSeparation κ
module FV = K8.FiniteVocabulary 𝒮
module CB = CardinalBridge 𝒮

open K4.Algebra 𝒮 using ( Pt ; _≤ᴮ_ ; ⊆ˢ-trans )
open K4.Algebra.Lattice Su.Ap.Ind.BAT.IC.codedLattice
  using ( _⊓ᴮ_ ; ⊤ᴮ ; ⊓-lb₁ ; ⊓-lb₂ ; ⊓-glb )
open K4.Implication 𝒮 Su.Ap.Ind.NG.extensional Su.Ap.Ind.NG.≈ˢ-paths
  Su.Ap.Ind.BAT.B Su.Ap.Ind.BAT.IC.codedLattice Su.Ap.Ind.BAT.IC.codedComplement
  using ( ≤ᴮ-antisym ; ⊤-greatest ; ⊓-⊤ )

open Su.Ap.Ind using ( checkNm ; emptyEnv ; emptyClause )
open Su.Ap using ( succClause ; indSrc )
open Su.Ap.Ind.BAT.Atomic using () renaming ( _∈ᴮ_ to mem )

ind-val : (σ : Su.Ap.Ind.VS.Nameᴮ)
  → Su.Ap.Ind.VS.val indSrc (σ ∷ emptyEnv)
    ≡ (Su.Ap.Ind.VS.val emptyClause (σ ∷ emptyEnv)
        ⊓ᴮ Su.Ap.Ind.VS.val succClause (σ ∷ emptyEnv))
ind-val σ = Su.Ap.Ind.VS.law-∧ emptyClause succClause (σ ∷ emptyEnv)

module FromEmpty
  (contains-check-empty : (e : S) → ⟨ FV.emptyPred e ⟩
    → (σ : Su.Ap.Ind.VS.Nameᴮ)
    → ⟨ Su.Ap.Ind.VS.val emptyClause (σ ∷ emptyEnv)
        ≤ᴮ mem (Su.Ap.Ind.BNG.Checked.check e) (fst σ) ⟩)
  where

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

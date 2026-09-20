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
import K4.Implication
import K8.FiniteVocabulary
import K10.CohenBooleanSuccApply

module K10.CohenBooleanLeastEmpty
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
open import FOL.Syntax using ( ⊥̇ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

module Ap = K10.CohenBooleanSuccApply 𝒮 families accessible images pow
  κ w lem hw paths
module FV = K8.FiniteVocabulary 𝒮

open K4.Algebra 𝒮 using ( Pt ; _≤ᴮ_ ; ⊆ˢ-trans )
open K4.Algebra.Lattice Ap.Ind.BAT.IC.codedLattice
  using ( _⊓ᴮ_ ; ⊤ᴮ ; ⊥ᴮ ; ⊓-lb₁ ; ⊓-lb₂ ; ⊓-glb )
open K4.Implication 𝒮 Ap.Ind.NG.extensional Ap.Ind.NG.≈ˢ-paths Ap.Ind.BAT.B
  Ap.Ind.BAT.IC.codedLattice Ap.Ind.BAT.IC.codedComplement
  using ( ≤ᴮ-antisym ; ⊤-greatest ; ⊓-⊤ ; ⇒ᴮ-curry ; ⇒ᴮ-mp ; _⇒ᴮ_ ; ⊥-least )

open Ap.Ind using ( checkNm ; emptyEnv ; emptyBody ; emptyClause
                  ; empty-mem-bot ; support-empty )
open Ap.Ind.BAT.Atomic using () renaming ( _∈ᴮ_ to mem ; _≈ᴮ_ to eq )

⇒-antiˡ : (a a' b : Pt Ap.Ind.BAT.B) → ⟨ a' ≤ᴮ a ⟩
  → ⟨ (a ⇒ᴮ b) ≤ᴮ (a' ⇒ᴮ b) ⟩
⇒-antiˡ a a' b h = ⇒ᴮ-curry (a ⇒ᴮ b) a' b
  (⊆ˢ-trans
    (⊓-glb (a ⇒ᴮ b) a ((a ⇒ᴮ b) ⊓ᴮ a')
      (⊓-lb₁ (a ⇒ᴮ b) a')
      (⊆ˢ-trans (⊓-lb₂ (a ⇒ᴮ b) a') h))
    (⇒ᴮ-mp a b))

weight-≤-mem : (n x : S) → ⟨ x ∈ˢ Ap.Ind.BNG.BSupport.support n ⟩
  → ⟨ Ap.Ind.BNG.weight n x ≤ᴮ mem x n ⟩
weight-≤-mem n x hx =
  subst (λ z → ⟨ z ≤ᴮ mem x n ⟩) (⊓-⊤ (Ap.Ind.BNG.weight n x))
    (subst (λ z → ⟨ (Ap.Ind.BNG.weight n x ⊓ᴮ z) ≤ᴮ mem x n ⟩)
      (Ap.Ind.BAT.Laws.≈ᴮ-refl x)
      (Ap.Ind.BAT.Atomic.∈ᴮ-ub x n x hx))

empty-body-le-eq : (e : S) → ⟨ FV.emptyPred e ⟩
  → (τ σ : Ap.Ind.VS.Nameᴮ)
  → ⟨ Ap.Ind.VS.val emptyBody (τ ∷ σ ∷ emptyEnv)
      ≤ᴮ eq (fst τ) (Ap.Ind.BNG.Checked.check e) ⟩
empty-body-le-eq e he τ σ =
  Ap.Ind.BAT.Atomic.≈ᴮ-glb (fst τ) (Ap.Ind.BNG.Checked.check e)
    (Ap.Ind.VS.val emptyBody (τ ∷ σ ∷ emptyEnv)) left right
  where
  left : (x : S) → ⟨ x ∈ˢ Ap.Ind.BNG.BSupport.support (fst τ) ⟩
    → ⟨ Ap.Ind.VS.val emptyBody (τ ∷ σ ∷ emptyEnv)
        ≤ᴮ (Ap.Ind.BNG.weight (fst τ) x ⇒ᴮ mem x (Ap.Ind.BNG.Checked.check e)) ⟩
  left x hx =
    subst (λ b → ⟨ Ap.Ind.VS.val emptyBody (τ ∷ σ ∷ emptyEnv)
                   ≤ᴮ (Ap.Ind.BNG.weight (fst τ) x ⇒ᴮ b) ⟩)
      (Ap.Ind.VS.law-⊥ (ν ∷ τ ∷ σ ∷ emptyEnv) ∙ sym (empty-mem-bot e he x))
      (⊆ˢ-trans
        (Ap.Ind.VS.law-∀∈-lb zero ⊥̇ (τ ∷ σ ∷ emptyEnv) ν)
        (⇒-antiˡ (mem x (fst τ)) (Ap.Ind.BNG.weight (fst τ) x)
          (Ap.Ind.VS.val ⊥̇ (ν ∷ τ ∷ σ ∷ emptyEnv))
          (weight-≤-mem (fst τ) x hx)))
    where
    ν : Ap.Ind.VS.Nameᴮ
    ν = x , Ap.Ind.BNG.BSupport.K.child-is-name (fst τ) (snd τ) x
      (Ap.Ind.BNG.BSupport.support-out (fst τ) x hx)
  right : (y : S) → ⟨ y ∈ˢ Ap.Ind.BNG.BSupport.support (Ap.Ind.BNG.Checked.check e) ⟩
    → ⟨ Ap.Ind.VS.val emptyBody (τ ∷ σ ∷ emptyEnv)
        ≤ᴮ (Ap.Ind.BNG.weight (Ap.Ind.BNG.Checked.check e) y
            ⇒ᴮ mem y (fst τ)) ⟩
  right y hy = Empty.rec* (support-empty e he y hy)

opaque
  contains-check-empty : (e : S) → ⟨ FV.emptyPred e ⟩
    → (σ : Ap.Ind.VS.Nameᴮ)
    → ⟨ Ap.Ind.VS.val emptyClause (σ ∷ emptyEnv)
        ≤ᴮ mem (Ap.Ind.BNG.Checked.check e) (fst σ) ⟩
  contains-check-empty e he σ =
    Ap.Ind.VS.law-∃∈-lub zero emptyBody (σ ∷ emptyEnv)
      (mem (Ap.Ind.BNG.Checked.check e) (fst σ)) λ τ →
        ⊆ˢ-trans
          (⊓-glb (eq (fst τ) (Ap.Ind.BNG.Checked.check e)) (mem (fst τ) (fst σ))
            (mem (fst τ) (fst σ) ⊓ᴮ Ap.Ind.VS.val emptyBody (τ ∷ σ ∷ emptyEnv))
            (⊆ˢ-trans (⊓-lb₂ (mem (fst τ) (fst σ))
              (Ap.Ind.VS.val emptyBody (τ ∷ σ ∷ emptyEnv)))
              (empty-body-le-eq e he τ σ))
            (⊓-lb₁ (mem (fst τ) (fst σ))
              (Ap.Ind.VS.val emptyBody (τ ∷ σ ∷ emptyEnv))))
          (Ap.Ind.BAT.Laws.∈ᴮ-congˡ (fst τ) (Ap.Ind.BNG.Checked.check e) (fst σ))

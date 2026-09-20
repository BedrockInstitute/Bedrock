{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile
import Cubical.HITs.PropositionalTruncation as PT
import K4.Algebra
import K9.BooleanNameGround
import K9.BooleanAtomic
import K10.CohenBooleanCands
import K10.CohenBooleanSubset
import K10.CohenBooleanPower

module K10.CohenBooleanPowerMem
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (families : NameKernel.Families 𝒮)
  (accessible : NameKernel.Accessibility 𝒮)
  (images : NameKernel.MemberImage 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (κ w : ZFStructure.S 𝒮)
  (lem : LEM ℓ)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open PT using ( ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

module Cands = K10.CohenBooleanCands 𝒮 families accessible images pow κ w
module Sub = K10.CohenBooleanSubset 𝒮 families accessible images pow κ w lem
module Power = K10.CohenBooleanPower 𝒮 families accessible images pow κ w lem
module BNG = K9.BooleanNameGround 𝒮 families accessible images pow κ w lem
open BNG using ( B ; weight ; weight-upper ; module BK ; module NG
               ; module IC ; module BSupport ; module Translation )
open NG using ( ≈ˢ-paths )
open K4.Algebra 𝒮 using ( Pt ; _≤ᴮ_ ; ⊆ˢ-trans )
open K4.Algebra.Lattice IC.codedLattice using ( _⊓ᴮ_ ; ⊓-glb ; ⊓-lb₁ ; ⊓-lb₂ )
module BAT = K9.BooleanAtomic.Atomic 𝒮 families accessible images pow κ w lem
  using ( _∈ᴮ_ ; _≈ᴮ_ ; ∈ᴮ-ub )

≈-refl : (a : S) → ⟨ a ≈ˢ a ⟩
≈-refl a = subst ⟨_⟩ (sym (≈ˢ-paths a a)) refl

cand-in-power : (σ : S) → ⟨ σ ∈ˢ Cands.cands ⟩
  → ⟨ Sub.candEntry σ ∈ˢ Power.powerB ⟩
cand-in-power σ hσ = subst ⟨_⟩ (sym (Power.powerB-spec (Sub.candEntry σ)))
  ∣ σ , ∣ hσ , ≈-refl (Sub.candEntry σ) ∣₁ ∣₁

entry-in-power : (σ : S) → ⟨ σ ∈ˢ Cands.cands ⟩
  → ⟨ BK.entry (Translation.trᴮ σ) (Sub.candWeight σ) ∈ˢ Power.powerB ⟩
entry-in-power σ hσ =
  subst (λ e → ⟨ e ∈ˢ Power.powerB ⟩) (Sub.candEntry-weight σ)
    (cand-in-power σ hσ)

cand-support : (σ : S) → ⟨ σ ∈ˢ Cands.cands ⟩
  → ⟨ Translation.trᴮ σ ∈ˢ BSupport.support Power.powerB ⟩
cand-support σ hσ = BSupport.entry-in Power.powerB (Translation.trᴮ σ)
  (Sub.candWeight σ) (Sub.candWeight-inB σ) (entry-in-power σ hσ)

⊓-monoˡ : (u u' v : Pt B) → ⟨ u ≤ᴮ u' ⟩ → ⟨ (u ⊓ᴮ v) ≤ᴮ (u' ⊓ᴮ v) ⟩
⊓-monoˡ u u' v h = ⊓-glb u' v (u ⊓ᴮ v)
  (⊆ˢ-trans (⊓-lb₁ u v) h) (⊓-lb₂ u v)

member-ub : (τ σ : S) → ⟨ σ ∈ˢ Cands.cands ⟩
  → ⟨ (Sub.subsetVal (Translation.trᴮ σ) ⊓ᴮ BAT._≈ᴮ_ τ (Translation.trᴮ σ))
      ≤ᴮ BAT._∈ᴮ_ τ Power.powerB ⟩
member-ub τ σ hσ = subst
  (λ b → ⟨ (b ⊓ᴮ BAT._≈ᴮ_ τ (Translation.trᴮ σ))
           ≤ᴮ BAT._∈ᴮ_ τ Power.powerB ⟩)
  (sym (Sub.candWeight-pt σ))
  (⊆ˢ-trans
    (⊓-monoˡ (Sub.candWeight σ , Sub.candWeight-inB σ)
      (weight Power.powerB (Translation.trᴮ σ))
      (BAT._≈ᴮ_ τ (Translation.trᴮ σ))
      (weight-upper Power.powerB (Translation.trᴮ σ)
        (Sub.candWeight σ , Sub.candWeight-inB σ)
        (entry-in-power σ hσ)))
    (BAT.∈ᴮ-ub τ Power.powerB (Translation.trᴮ σ) (cand-support σ hσ)))

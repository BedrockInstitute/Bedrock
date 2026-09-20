{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile
import Cubical.HITs.PropositionalTruncation as PT
import K4.Algebra
import K4.ValueSets
import K9.BooleanNameGround
import K9.BooleanAtomic
import K10.CohenBooleanSubset

module K10.CohenBooleanSubsetVal
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
open NameKernel.MemberImage images using ( image ; image-spec )

module Sub = K10.CohenBooleanSubset 𝒮 families accessible images pow κ w lem
module BNG = Sub.BNG
open BNG using ( B ; weight ; module NG ; module IC ; module BSupport )
open NG using ( extensional ; ≈ˢ-paths )
open K4.Algebra 𝒮 using ( Pt ; _≤ᴮ_ ; Pt≡ )
open K4.Algebra.CodedComplete IC.codedComplete using ( inf-lb ; inf-glb )
module BAT = K9.BooleanAtomic.Atomic 𝒮 families accessible images pow κ w lem
  using ( _∈ᴮ_ )

module VS = K4.ValueSets.Core 𝒮 extensional ≈ˢ-paths B IC.codedLattice IC.codedComplete
private
  values = VS.member→values image image-spec
  module Values = VS.ValueSets values

≈-refl : (a : S) → ⟨ a ≈ˢ a ⟩
≈-refl a = subst ⟨_⟩ (sym (≈ˢ-paths a a)) refl

subset-lb : (χ x : S) (hx : ⟨ x ∈ˢ BSupport.support χ ⟩)
  → ⟨ Sub.subsetVal χ ≤ᴮ Sub.subsetFam χ (x , hx) ⟩
subset-lb χ x hx = inf-lb
  (Values.attain (BSupport.support χ) (Sub.subsetFam χ))
  (Values.attain-sub (BSupport.support χ) (Sub.subsetFam χ))
  (Sub.subsetFam χ (x , hx))
  (subst ⟨_⟩ (sym (Values.attain-spec (BSupport.support χ)
    (Sub.subsetFam χ) (fst (Sub.subsetFam χ (x , hx)))))
    ∣ x , ∣ hx , ≈-refl (fst (Sub.subsetFam χ (x , hx))) ∣₁ ∣₁ )

≈→≡ : {a b : S} → ⟨ a ≈ˢ b ⟩ → a ≡ b
≈→≡ {a} {b} = subst ⟨_⟩ (≈ˢ-paths a b)

subset-glb : (χ : S) (v : Pt B)
  → ((x : S) (hx : ⟨ x ∈ˢ BSupport.support χ ⟩)
      → ⟨ v ≤ᴮ Sub.subsetFam χ (x , hx) ⟩)
  → ⟨ v ≤ᴮ Sub.subsetVal χ ⟩
subset-glb χ v hyp = inf-glb
  (Values.attain (BSupport.support χ) (Sub.subsetFam χ))
  (Values.attain-sub (BSupport.support χ) (Sub.subsetFam χ))
  v λ u hu → PT.rec (snd (v ≤ᴮ u))
    (λ { (x , inner) → PT.rec (snd (v ≤ᴮ u))
      (λ { (hx , heq) →
        subst (λ z → ⟨ v ≤ᴮ z ⟩)
          (sym (Pt≡ {B} {u} {Sub.subsetFam χ (x , hx)} (≈→≡ heq)))
          (hyp x hx) })
      inner })
    (subst ⟨_⟩ (Values.attain-spec (BSupport.support χ)
      (Sub.subsetFam χ) (fst u)) hu)


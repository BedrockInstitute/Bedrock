{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile
import Cubical.HITs.PropositionalTruncation as PT
import K4.Algebra
import K4.Implication
import K9.BooleanAtomic
import K9.BooleanNameGround
import K9.NameGround
import K10.CohenBooleanMiximal
import K10.CohenBooleanMiximalApprox
import K10.CohenBooleanMiximalCover
import K10.CohenBooleanSubset
import K10.CohenBooleanSubsetVal

module K10.CohenBooleanMiximalLeft
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

module NG = K9.NameGround 𝒮 families accessible images pow κ w
module Mx = K10.CohenBooleanMiximal 𝒮 families accessible images pow κ w lem
module Cv = K10.CohenBooleanMiximalCover 𝒮 families accessible images pow κ w lem
module Sub = K10.CohenBooleanSubset 𝒮 families accessible images pow κ w lem
module SV = K10.CohenBooleanSubsetVal 𝒮 families accessible images pow κ w lem
module BNG = K9.BooleanNameGround 𝒮 families accessible images pow κ w lem
open BNG using ( B ; weight ; weight-least ; weight-upper ; entry-agrees
               ; source-entry-in
               ; module Translation ; module BK ; module BSupport ; module Base ; module IC )
module BAT = K9.BooleanAtomic.Atomic 𝒮 families accessible images pow κ w lem
  using ( _∈ᴮ_ ; _≈ᴮ_ ; ∈ᴮ-ub ; ∈ᴮ-lub )
module Laws = K9.BooleanAtomic.Laws 𝒮 families accessible images pow κ w lem
  using ( ≈ᴮ-refl ; ∈ᴮ-congˡ )
open NameKernel.MemberImage images using ( image-spec )
open K4.Algebra 𝒮 using ( Pt ; _≤ᴮ_ ; ⊆ˢ-trans ; ≤ᴮ-refl ; Pt≡ )
open K4.Algebra.Lattice IC.codedLattice
  using ( ⊤ᴮ ; ⊥ᴮ ; _⊓ᴮ_ ; ⊓-lb₁ ; ⊓-lb₂ ; ⊓-glb ; ⊥-least ; ⊤-greatest )
open K4.Algebra.CodedComplete IC.codedComplete using ( sup-lub )
open K4.Implication 𝒮 NG.extensional NG.≈ˢ-paths B IC.codedLattice IC.codedComplement
  using ( _⇒ᴮ_ ; ⇒ᴮ-curry ; ⇒ᴮ-uncurry ; ⊓-⊤ ; ⊓-comm ; ≤ᴮ-antisym )
open NG using ( extensional ; ≈ˢ-paths )
open NG.GS using ( ≈→≡ )

omega : S
omega = Translation.trᴮ (NG.Check.chk w)

miximalNm : S → S
miximalNm τ = Translation.trᴮ (Mx.miximalOf τ)

mem-from-weight : (x n y : S)
  → ⟨ (weight n y ⊓ᴮ BAT._≈ᴮ_ x y) ≤ᴮ BAT._∈ᴮ_ x n ⟩
mem-from-weight x n y =
  ⇒ᴮ-uncurry (weight n y) (BAT._≈ᴮ_ x y) (BAT._∈ᴮ_ x n)
    (weight-least n y (BAT._≈ᴮ_ x y ⇒ᴮ BAT._∈ᴮ_ x n) λ b he →
      ⊆ˢ-trans
        (weight-upper n y b he)
        (⇒ᴮ-curry (weight n y) (BAT._≈ᴮ_ x y) (BAT._∈ᴮ_ x n)
          (BAT.∈ᴮ-ub x n y
            (BSupport.entry-in n y (fst b) (snd b) he))))

omega-child : (y : S)
  → ⟨ y ∈ˢ BSupport.support omega ⟩
  → PT.∥ Σ[ z ∈ S ] (⟨ z ∈ˢ Mx.omegaDom ⟩ × (y ≡ Translation.trᴮ z)) ∥₁
omega-child y hy = PT.rec PT.squash₁
  (λ { (b , hb , he) → PT.rec PT.squash₁
    (λ { (z , inner₁) → PT.rec PT.squash₁
      (λ { (p , inner₂) → PT.rec PT.squash₁
        (λ { (hp , hen , heq) →
          ∣ z
          , source-entry-in (NG.Check.chk w) z p hp hen
          , fst (BK.entry-inj (≈→≡ heq)) ∣₁ })
        inner₂ })
      inner₁ })
    (subst ⟨_⟩ (Translation.trᴮ-entries (NG.Check.chk w)
      (BK.entry y b)) he) })
  (BSupport.entry-out omega y hy)

⊓-monoˡ : (u u' v : Pt B) → ⟨ u ≤ᴮ u' ⟩ → ⟨ (u ⊓ᴮ v) ≤ᴮ (u' ⊓ᴮ v) ⟩
⊓-monoˡ u u' v h = ⊓-glb u' v (u ⊓ᴮ v)
  (⊆ˢ-trans (⊓-lb₁ u v) h) (⊓-lb₂ u v)

drop-weight : (x τ y : S)
  → ⟨ ((weight omega y ⊓ᴮ BAT._≈ᴮ_ x y) ⊓ᴮ BAT._∈ᴮ_ x τ)
      ≤ᴮ (BAT._≈ᴮ_ x y ⊓ᴮ BAT._∈ᴮ_ x τ) ⟩
drop-weight x τ y =
  ⊓-glb (BAT._≈ᴮ_ x y) (BAT._∈ᴮ_ x τ)
    ((weight omega y ⊓ᴮ BAT._≈ᴮ_ x y) ⊓ᴮ BAT._∈ᴮ_ x τ)
    (⊆ˢ-trans
      (⊓-lb₁ (weight omega y ⊓ᴮ BAT._≈ᴮ_ x y) (BAT._∈ᴮ_ x τ))
      (⊓-lb₂ (weight omega y) (BAT._≈ᴮ_ x y)))
    (⊓-lb₂ (weight omega y ⊓ᴮ BAT._≈ᴮ_ x y) (BAT._∈ᴮ_ x τ))

cong-meet : (x τ y t : S) → y ≡ t
  → ⟨ (BAT._≈ᴮ_ x y ⊓ᴮ BAT._∈ᴮ_ x τ)
      ≤ᴮ (BAT._∈ᴮ_ t τ ⊓ᴮ BAT._≈ᴮ_ x t) ⟩
cong-meet x τ y t y≡ =
  subst (λ s → ⟨ (BAT._≈ᴮ_ x y ⊓ᴮ BAT._∈ᴮ_ x τ)
                ≤ᴮ (BAT._∈ᴮ_ s τ ⊓ᴮ BAT._≈ᴮ_ x s) ⟩) y≡
    (⊓-glb (BAT._∈ᴮ_ y τ) (BAT._≈ᴮ_ x y)
      (BAT._≈ᴮ_ x y ⊓ᴮ BAT._∈ᴮ_ x τ)
      (Laws.∈ᴮ-congˡ x y τ)
      (⊓-lb₁ (BAT._≈ᴮ_ x y) (BAT._∈ᴮ_ x τ)))

cover-at : (x τ y : S)
  → ⟨ y ∈ˢ BSupport.support omega ⟩
  → ⟨ ((weight omega y ⊓ᴮ BAT._≈ᴮ_ x y) ⊓ᴮ BAT._∈ᴮ_ x τ)
      ≤ᴮ BAT._∈ᴮ_ x (miximalNm τ) ⟩
cover-at x τ y hy = PT.rec
  (snd (((weight omega y ⊓ᴮ BAT._≈ᴮ_ x y) ⊓ᴮ BAT._∈ᴮ_ x τ)
        ≤ᴮ BAT._∈ᴮ_ x (miximalNm τ)))
  from-child (omega-child y hy)
  where
  from-child : Σ[ z ∈ S ] (⟨ z ∈ˢ Mx.omegaDom ⟩ × (y ≡ Translation.trᴮ z))
    → ⟨ ((weight omega y ⊓ᴮ BAT._≈ᴮ_ x y) ⊓ᴮ BAT._∈ᴮ_ x τ)
        ≤ᴮ BAT._∈ᴮ_ x (miximalNm τ) ⟩
  from-child (z , hz , y≡) = ⊆ˢ-trans (drop-weight x τ y)
    (⊆ˢ-trans (cong-meet x τ y (Translation.trᴮ z) y≡)
      (⊆ˢ-trans
        (⊓-monoˡ (BAT._∈ᴮ_ (Translation.trᴮ z) τ)
          (weight (miximalNm τ) (Translation.trᴮ z))
          (BAT._≈ᴮ_ x (Translation.trᴮ z))
          (Cv.weight-tr-ge τ z hz))
        (mem-from-weight x (miximalNm τ) (Translation.trᴮ z))))

cover-mem : (x τ : S)
  → ⟨ (BAT._∈ᴮ_ x omega ⊓ᴮ BAT._∈ᴮ_ x τ)
      ≤ᴮ BAT._∈ᴮ_ x (miximalNm τ) ⟩
cover-mem x τ = ⇒ᴮ-uncurry (BAT._∈ᴮ_ x omega) (BAT._∈ᴮ_ x τ)
  (BAT._∈ᴮ_ x (miximalNm τ))
  (BAT.∈ᴮ-lub x omega (BAT._∈ᴮ_ x τ ⇒ᴮ BAT._∈ᴮ_ x (miximalNm τ)) λ y hy →
    ⇒ᴮ-curry (weight omega y ⊓ᴮ BAT._≈ᴮ_ x y)
      (BAT._∈ᴮ_ x τ) (BAT._∈ᴮ_ x (miximalNm τ))
      (cover-at x τ y hy))

weight≤mem : (χ x : S) → ⟨ x ∈ˢ BSupport.support χ ⟩
  → ⟨ weight χ x ≤ᴮ BAT._∈ᴮ_ x χ ⟩
weight≤mem χ x hx =
  subst (λ z → ⟨ z ≤ᴮ BAT._∈ᴮ_ x χ ⟩) (⊓-⊤ (weight χ x))
    (subst (λ z → ⟨ (weight χ x ⊓ᴮ z) ≤ᴮ BAT._∈ᴮ_ x χ ⟩)
      (Laws.≈ᴮ-refl x)
      (BAT.∈ᴮ-ub x χ x hx))

opaque
  miximal-left : (τ x : S) → ⟨ x ∈ˢ BSupport.support τ ⟩
    → ⟨ Sub.subsetVal τ
        ≤ᴮ (weight τ x ⇒ᴮ BAT._∈ᴮ_ x (miximalNm τ)) ⟩
  miximal-left τ x hx = ⇒ᴮ-curry (Sub.subsetVal τ) (weight τ x)
    (BAT._∈ᴮ_ x (miximalNm τ))
    (⊆ˢ-trans meet-omega-τ (cover-mem x τ))
    where
    meet-omega : ⟨ (Sub.subsetVal τ ⊓ᴮ weight τ x) ≤ᴮ BAT._∈ᴮ_ x omega ⟩
    meet-omega = ⇒ᴮ-uncurry (Sub.subsetVal τ) (weight τ x)
      (BAT._∈ᴮ_ x omega) (SV.subset-lb τ x hx)
    meet-τ : ⟨ (Sub.subsetVal τ ⊓ᴮ weight τ x) ≤ᴮ BAT._∈ᴮ_ x τ ⟩
    meet-τ = ⊆ˢ-trans (⊓-lb₂ (Sub.subsetVal τ) (weight τ x))
      (weight≤mem τ x hx)
    meet-omega-τ : ⟨ (Sub.subsetVal τ ⊓ᴮ weight τ x)
                     ≤ᴮ (BAT._∈ᴮ_ x omega ⊓ᴮ BAT._∈ᴮ_ x τ) ⟩
    meet-omega-τ = ⊓-glb (BAT._∈ᴮ_ x omega) (BAT._∈ᴮ_ x τ)
      (Sub.subsetVal τ ⊓ᴮ weight τ x) meet-omega meet-τ

module FL = K10.CohenBooleanMiximalApprox.FromLeft
  𝒮 families accessible images pow κ w lem miximal-left

approx-eq : (τ : S)
  → ⟨ Sub.subsetVal τ ≤ᴮ BAT._≈ᴮ_ τ (miximalNm τ) ⟩
approx-eq = FL.approx-eq

miximal-child : (τ y : S)
  → ⟨ y ∈ˢ BSupport.support (miximalNm τ) ⟩
  → PT.∥ Σ[ z ∈ S ] (⟨ z ∈ˢ Mx.omegaDom ⟩ × (y ≡ Translation.trᴮ z)) ∥₁
miximal-child τ y hy = PT.rec PT.squash₁
  (λ { (b , hb , he) → PT.rec PT.squash₁
    (λ { (z , inner₁) → PT.rec PT.squash₁
      (λ { (p , inner₂) → PT.rec PT.squash₁
        (λ { (hp , hen , heq) → PT.rec PT.squash₁
          (λ { (z' , hz' , ps) → PT.rec PT.squash₁
            (λ { (p' , hp' , ep) →
              ∣ z'
              , hz'
              , fst (BK.entry-inj (≈→≡ heq))
                ∙ cong Translation.trᴮ (fst (NG.K.entry-inj (≈→≡ ep))) ∣₁ })
            ps })
          (subst ⟨_⟩ (Mx.miximal-spec τ (NG.K.entry z p))
            (subst (λ e → ⟨ e ∈ˢ Mx.miximalOf τ ⟩) (entry-agrees z p) hen)) })
        inner₂ })
      inner₁ })
    (subst ⟨_⟩ (Translation.trᴮ-entries (Mx.miximalOf τ)
      (BK.entry y b)) he) })
  (BSupport.entry-out (miximalNm τ) y hy)

omega-entry-all : (z q : S)
  → ⟨ z ∈ˢ Mx.omegaDom ⟩
  → ⟨ q ∈ˢ NG.C.carrier ⟩
  → ⟨ BK.entry z q ∈ˢ NG.Check.chk w ⟩
omega-entry-all z q hz hq = PT.rec (snd (BK.entry z q ∈ˢ NG.Check.chk w))
  (λ { (p , hp , he) → PT.rec (snd (BK.entry z q ∈ˢ NG.Check.chk w))
    (λ { (y , hy , inner) → PT.rec (snd (BK.entry z q ∈ˢ NG.Check.chk w))
      (λ { (p' , hp' , ep) →
        let z≡ = fst (NG.K.entry-inj (≈→≡ ep))
        in subst ⟨_⟩ (sym (NG.Check.chk-spec w (BK.entry z q)))
          ∣ y , hy ,
            ∣ q , hq ,
              subst ⟨_⟩ (sym (≈ˢ-paths (BK.entry z q)
                (NG.K.entry (NG.Check.chk y) q)))
                (entry-agrees z q
                  ∙ cong (λ t → NG.K.entry t q) z≡)
            ∣₁
          ∣₁ })
      inner })
    (subst ⟨_⟩ (NG.Check.chk-spec w (NG.K.entry z p))
      (subst (λ e → ⟨ e ∈ˢ NG.Check.chk w ⟩) (entry-agrees z p) he)) })
  (BNG.source-entry-out (NG.Check.chk w) z hz)

tr-omega-entry : (z q : S) (hq : ⟨ q ∈ˢ NG.C.carrier ⟩)
  → ⟨ BK.entry z q ∈ˢ NG.Check.chk w ⟩
  → ⟨ BK.entry (Translation.trᴮ z) (fst (Base.iᴷ (q , hq))) ∈ˢ omega ⟩
tr-omega-entry z q hq hen =
  subst ⟨_⟩ (sym (Translation.trᴮ-entries (NG.Check.chk w)
    (BK.entry (Translation.trᴮ z) (fst (Base.iᴷ (q , hq))))))
    ∣ z , ∣ q , ∣ hq , hen , Cv.≈-refl (BK.entry (Translation.trᴮ z)
      (fst (Base.iᴷ (q , hq)))) ∣₁ ∣₁ ∣₁

omega-weight-top : (z : S) → ⟨ z ∈ˢ Mx.omegaDom ⟩
  → ⟨ ⊤ᴮ ≤ᴮ weight omega (Translation.trᴮ z) ⟩
omega-weight-top z hz =
  subst (λ u → ⟨ u ≤ᴮ weight omega (Translation.trᴮ z) ⟩)
    (Cv.recover ⊤ᴮ)
    (sup-lub
      (Cv.iFamily ⊤ᴮ) (Cv.iFamily-sub ⊤ᴮ)
      (weight omega (Translation.trᴮ z)) λ u hu →
      PT.rec (snd (u ≤ᴮ weight omega (Translation.trᴮ z)))
        (λ { (q , inner) → PT.rec (snd (u ≤ᴮ weight omega (Translation.trᴮ z)))
          (λ { (hq , heq) →
            subst (λ v → ⟨ v ≤ᴮ weight omega (Translation.trᴮ z) ⟩)
              (sym (Pt≡ {B} {u}
                {Base.iᴷ (q , Cv.inCar ⊤ᴮ q hq)} (≈→≡ heq)))
              (weight-upper omega (Translation.trᴮ z)
                (Base.iᴷ (q , Cv.inCar ⊤ᴮ q hq))
                (tr-omega-entry z q (Cv.inCar ⊤ᴮ q hq)
                  (omega-entry-all z q hz (Cv.inCar ⊤ᴮ q hq)))) })
          inner })
        (subst ⟨_⟩ (image-spec
          (fst ⊤ᴮ)
          (λ r → fst (Base.iᴷ (fst r , Cv.inCar ⊤ᴮ (fst r) (snd r))))
          (fst u)) hu))


omega-support : (z : S) → ⟨ z ∈ˢ Mx.omegaDom ⟩
  → ⟨ Translation.trᴮ z ∈ˢ BSupport.support omega ⟩
omega-support z hz = PT.rec (snd (Translation.trᴮ z ∈ˢ BSupport.support omega))
  (λ { (q , hq , he) →
    BSupport.entry-in omega (Translation.trᴮ z)
      (fst (Base.iᴷ (q , hq))) (snd (Base.iᴷ (q , hq)))
      (tr-omega-entry z q hq he) })
  (BNG.source-entry-out (NG.Check.chk w) z hz)

omega-in-top : (z : S) → ⟨ z ∈ˢ Mx.omegaDom ⟩
  → BAT._∈ᴮ_ (Translation.trᴮ z) omega ≡ ⊤ᴮ
omega-in-top z hz = ≤ᴮ-antisym (⊤-greatest (BAT._∈ᴮ_ (Translation.trᴮ z) omega))
  (⊆ˢ-trans (omega-weight-top z hz)
    (weight≤mem omega (Translation.trᴮ z) (omega-support z hz)))

opaque
  subsetVal-le : (τ : S)
    → ⟨ Sub.subsetVal τ ≤ᴮ Sub.subsetVal (miximalNm τ) ⟩
  subsetVal-le τ = SV.subset-glb (miximalNm τ) (Sub.subsetVal τ)
    λ y hy → PT.rec (snd (Sub.subsetVal τ ≤ᴮ Sub.subsetFam (miximalNm τ) (y , hy)))
      (λ { (z , hz , y≡) →
        subst (λ t → ⟨ Sub.subsetVal τ
                        ≤ᴮ (weight (miximalNm τ) t ⇒ᴮ BAT._∈ᴮ_ t omega) ⟩)
          (sym y≡)
          (subst (λ b → ⟨ Sub.subsetVal τ
                           ≤ᴮ (weight (miximalNm τ) (Translation.trᴮ z) ⇒ᴮ b) ⟩)
            (sym (omega-in-top z hz))
            (subst (λ z → ⟨ Sub.subsetVal τ ≤ᴮ z ⟩)
              (sym (Cv.⇒ᴮ-from-≤ (weight (miximalNm τ) (Translation.trᴮ z)) ⊤ᴮ
                (⊤-greatest (weight (miximalNm τ) (Translation.trᴮ z)))))
              (⊤-greatest (Sub.subsetVal τ)))) })
      (miximal-child τ y hy)

opaque
  covering : (τ : S)
    → ⟨ Sub.subsetVal τ
        ≤ᴮ (Sub.subsetVal (miximalNm τ) ⊓ᴮ BAT._≈ᴮ_ τ (miximalNm τ)) ⟩
  covering τ = FL.approx-meet τ (subsetVal-le τ)

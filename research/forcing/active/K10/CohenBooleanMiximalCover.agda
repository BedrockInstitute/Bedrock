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
import K5.Frame
import K9.BooleanAtomic
import K9.BooleanNameGround
import K9.NameGround
import K10.CohenBooleanMiximal

module K10.CohenBooleanMiximalCover
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (families : NameKernel.Families 𝒮)
  (accessible : NameKernel.Accessibility 𝒮)
  (images : NameKernel.MemberImage 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (κ w : ZFStructure.S 𝒮)
  (lem : LEM ℓ)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.ZFModel 𝒮 using ( _⊆ˢ_ )
open PT using ( ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

module NG = K9.NameGround 𝒮 families accessible images pow κ w
module Mx = K10.CohenBooleanMiximal 𝒮 families accessible images pow κ w lem
module BNG = K9.BooleanNameGround 𝒮 families accessible images pow κ w lem
open BNG using ( B ; weight ; weight-least ; weight-upper ; entry-agrees
               ; module Translation ; module BK ; module BSupport ; module Base ; module IC )
module BAT = K9.BooleanAtomic.Atomic 𝒮 families accessible images pow κ w lem
  using ( _∈ᴮ_ )
open NameKernel.MemberImage images using ( image ; image-spec )
open K4.Algebra 𝒮 using ( Pt ; _≤ᴮ_ ; ⊆ˢ-trans ; Pt≡ ; ≤ᴮ-refl )
open K4.Algebra.Lattice IC.codedLattice using ( ⊤ᴮ ; ⊤-greatest ; _⊓ᴮ_ ; ⊓-lb₂ )
open K4.Algebra.CodedComplete IC.codedComplete using ( supᴮ ; sup-ub ; sup-lub )
open K4.Implication 𝒮 NG.extensional NG.≈ˢ-paths B IC.codedLattice IC.codedComplement
  using ( _⇒ᴮ_ ; ⇒ᴮ-curry ; ≤ᴮ-antisym )
open NG using ( extensional ; ≈ˢ-paths )
open NG.GS using ( ≈→≡ )

open K5.Frame.Poset.ForcingBase (Base.codedBase lem)
  using ( i ; below-out ; below-in )

weight-tr-le : (τ y : S)
  → ⟨ y ∈ˢ BSupport.support (Translation.trᴮ (Mx.miximalOf τ)) ⟩
  → ⟨ weight (Translation.trᴮ (Mx.miximalOf τ)) y
      ≤ᴮ BAT._∈ᴮ_ y τ ⟩
weight-tr-le τ y hy =
  weight-least (Translation.trᴮ (Mx.miximalOf τ)) y (BAT._∈ᴮ_ y τ)
    λ b he → PT.rec (snd (b ≤ᴮ BAT._∈ᴮ_ y τ))
      (λ { (x , inner₁) → PT.rec (snd (b ≤ᴮ BAT._∈ᴮ_ y τ))
        (λ { (p , inner₂) → PT.rec (snd (b ≤ᴮ BAT._∈ᴮ_ y τ))
          (λ { (hp , hen , heq) → from-entry b x p hp hen heq })
          inner₂ })
        inner₁ })
      (subst ⟨_⟩ (Translation.trᴮ-entries (Mx.miximalOf τ)
        (BK.entry y (fst b))) he)
  where
  from-entry : (b : Pt B) (x p : S) (hp : ⟨ p ∈ˢ NG.C.carrier ⟩)
    → ⟨ BK.entry x p ∈ˢ Mx.miximalOf τ ⟩
    → ⟨ BK.entry y (fst b) ≈ˢ BK.entry (Translation.trᴮ x)
          (fst (Base.iᴷ (p , hp))) ⟩
    → ⟨ b ≤ᴮ BAT._∈ᴮ_ y τ ⟩
  from-entry b x p hp hen heq = PT.rec (snd (b ≤ᴮ BAT._∈ᴮ_ y τ))
    (λ { (x' , hx' , ps) → PT.rec (snd (b ≤ᴮ BAT._∈ᴮ_ y τ))
      (λ { (p' , hp' , ep) →
        let same = NG.K.entry-inj (≈→≡ ep)
        in subst (λ z → ⟨ b ≤ᴮ BAT._∈ᴮ_ z τ ⟩) (sym y≡trx)
          (from-mem x' p' hx' hp' (fst same) (snd same)) })
      ps })
    (subst ⟨_⟩ (Mx.miximal-spec τ (NG.K.entry x p)) henK)
    where
    pair : (y ≡ Translation.trᴮ x) × (fst b ≡ fst (Base.iᴷ (p , hp)))
    pair = BK.entry-inj (≈→≡ heq)
    y≡trx : y ≡ Translation.trᴮ x
    y≡trx = fst pair
    b≡i : fst b ≡ fst (Base.iᴷ (p , hp))
    b≡i = snd pair
    henK : ⟨ NG.K.entry x p ∈ˢ Mx.miximalOf τ ⟩
    henK = subst (λ e → ⟨ e ∈ˢ Mx.miximalOf τ ⟩) (entry-agrees x p) hen
    from-mem : (x' p' : S)
      → ⟨ x' ∈ˢ Mx.omegaDom ⟩
      → ⟨ p' ∈ˢ Mx.memCode x' τ ⟩
      → x ≡ x'
      → p ≡ p'
      → ⟨ b ≤ᴮ BAT._∈ᴮ_ (Translation.trᴮ x) τ ⟩
    from-mem x' p' hx' hp' x≡x' p≡p' =
      subst (λ u → ⟨ u ≤ᴮ BAT._∈ᴮ_ (Translation.trᴮ x) τ ⟩)
        (sym (Pt≡ {B} {b} {Base.iᴷ (p , hp)} b≡i))
        (subst (λ z → ⟨ Base.iᴷ (p , hp) ≤ᴮ BAT._∈ᴮ_ (Translation.trᴮ z) τ ⟩)
          (sym x≡x')
          (below-out (BAT._∈ᴮ_ (Translation.trᴮ x') τ) (p , hp)
            (subst (λ z → ⟨ z ∈ˢ fst (BAT._∈ᴮ_ (Translation.trᴮ x') τ) ⟩)
              (sym p≡p') hp')))

⇒ᴮ-from-≤ : (a b : Pt B) → ⟨ a ≤ᴮ b ⟩ → (a ⇒ᴮ b) ≡ ⊤ᴮ
⇒ᴮ-from-≤ a b h = ≤ᴮ-antisym (⊤-greatest (a ⇒ᴮ b))
  (⇒ᴮ-curry ⊤ᴮ a b (⊆ˢ-trans (⊓-lb₂ ⊤ᴮ a) h))

opaque
  miximal-right : (τ y : S) (c : Pt B)
    → ⟨ y ∈ˢ BSupport.support (Translation.trᴮ (Mx.miximalOf τ)) ⟩
    → ⟨ c ≤ᴮ (weight (Translation.trᴮ (Mx.miximalOf τ)) y
               ⇒ᴮ BAT._∈ᴮ_ y τ) ⟩
  miximal-right τ y c hy =
    subst (λ z → ⟨ c ≤ᴮ z ⟩)
      (sym (⇒ᴮ-from-≤ (weight (Translation.trᴮ (Mx.miximalOf τ)) y)
        (BAT._∈ᴮ_ y τ) (weight-tr-le τ y hy)))
      (⊤-greatest c)

≈-refl : (a : S) → ⟨ a ≈ˢ a ⟩
≈-refl a = subst ⟨_⟩ (sym (≈ˢ-paths a a)) refl

tr-entry : (τ x p : S) (hp : ⟨ p ∈ˢ NG.C.carrier ⟩)
  → ⟨ BK.entry x p ∈ˢ Mx.miximalOf τ ⟩
  → ⟨ BK.entry (Translation.trᴮ x) (fst (Base.iᴷ (p , hp)))
        ∈ˢ Translation.trᴮ (Mx.miximalOf τ) ⟩
tr-entry τ x p hp hen =
  subst ⟨_⟩ (sym (Translation.trᴮ-entries (Mx.miximalOf τ)
    (BK.entry (Translation.trᴮ x) (fst (Base.iᴷ (p , hp))))))
    ∣ x , ∣ p , ∣ hp , hen , ≈-refl (BK.entry (Translation.trᴮ x)
      (fst (Base.iᴷ (p , hp)))) ∣₁ ∣₁ ∣₁

weight-principal : (τ x p : S) (hp : ⟨ p ∈ˢ NG.C.carrier ⟩)
  → ⟨ BK.entry x p ∈ˢ Mx.miximalOf τ ⟩
  → ⟨ Base.iᴷ (p , hp) ≤ᴮ weight (Translation.trᴮ (Mx.miximalOf τ))
        (Translation.trᴮ x) ⟩
weight-principal τ x p hp hen =
  weight-upper (Translation.trᴮ (Mx.miximalOf τ)) (Translation.trᴮ x)
    (Base.iᴷ (p , hp))
    (tr-entry τ x p hp hen)

inCar : (b : Pt B) (p : S) → ⟨ p ∈ˢ fst b ⟩ → ⟨ p ∈ˢ NG.C.carrier ⟩
inCar b p hp =
  subst (λ z → ⟨ p ∈ˢ z ⟩) top-is-carrier (⊤-greatest b p hp)
  where
  top-is-carrier : fst ⊤ᴮ ≡ NG.C.carrier
  top-is-carrier = refl

iFamily : Pt B → S
iFamily b = image (fst b) (λ q → fst (Base.iᴷ (fst q , inCar b (fst q) (snd q))))

iFamily-sub : (b : Pt B) → ⟨ iFamily b ⊆ˢ B ⟩
iFamily-sub b z hz = PT.rec (snd (z ∈ˢ B))
  (λ { (p , inner) → PT.rec (snd (z ∈ˢ B))
    (λ { (hp , heq) →
      subst (λ w → ⟨ w ∈ˢ B ⟩) (sym (≈→≡ heq))
        (snd (Base.iᴷ (p , inCar b p hp))) })
    inner })
  (subst ⟨_⟩ (image-spec (fst b)
    (λ q → fst (Base.iᴷ (fst q , inCar b (fst q) (snd q)))) z) hz)

i-self : (p : S) (hp : ⟨ p ∈ˢ NG.C.carrier ⟩)
  → ⟨ p ∈ˢ fst (Base.iᴷ (p , hp)) ⟩
i-self p hp = below-in (Base.iᴷ (p , hp)) (p , hp)
  (≤ᴮ-refl (Base.iᴷ (p , hp)))

recover : (b : Pt B) → supᴮ (iFamily b) (iFamily-sub b) ≡ b
recover b = ≤ᴮ-antisym down up
  where
  down : ⟨ supᴮ (iFamily b) (iFamily-sub b) ≤ᴮ b ⟩
  down = sup-lub (iFamily b) (iFamily-sub b) b λ u hu →
    PT.rec (snd (u ≤ᴮ b))
      (λ { (p , inner) → PT.rec (snd (u ≤ᴮ b))
        (λ { (hp , heq) →
          subst (λ v → ⟨ v ≤ᴮ b ⟩)
            (sym (Pt≡ {B} {u} {Base.iᴷ (p , inCar b p hp)} (≈→≡ heq)))
            (below-out b (p , inCar b p hp) hp) })
        inner })
      (subst ⟨_⟩ (image-spec (fst b)
        (λ q → fst (Base.iᴷ (fst q , inCar b (fst q) (snd q)))) (fst u)) hu)

  up : ⟨ b ≤ᴮ supᴮ (iFamily b) (iFamily-sub b) ⟩
  up q hq =
    let iq = Base.iᴷ (q , inCar b q hq)
        inFam : ⟨ fst iq ∈ˢ iFamily b ⟩
        inFam = subst ⟨_⟩ (sym (image-spec (fst b)
          (λ r → fst (Base.iᴷ (fst r , inCar b (fst r) (snd r)))) (fst iq)))
          ∣ q , ∣ hq , subst ⟨_⟩ (sym (≈ˢ-paths (fst iq) (fst iq))) refl ∣₁ ∣₁
    in sup-ub (iFamily b) (iFamily-sub b) iq inFam q (i-self q (inCar b q hq))

weight-tr-ge : (τ z : S) → ⟨ z ∈ˢ Mx.omegaDom ⟩
  → ⟨ BAT._∈ᴮ_ (Translation.trᴮ z) τ
      ≤ᴮ weight (Translation.trᴮ (Mx.miximalOf τ)) (Translation.trᴮ z) ⟩
weight-tr-ge τ z hz =
  subst (λ u → ⟨ u ≤ᴮ weight (Translation.trᴮ (Mx.miximalOf τ))
                    (Translation.trᴮ z) ⟩)
    (recover (BAT._∈ᴮ_ (Translation.trᴮ z) τ))
    (sup-lub (iFamily (BAT._∈ᴮ_ (Translation.trᴮ z) τ))
      (iFamily-sub (BAT._∈ᴮ_ (Translation.trᴮ z) τ))
      (weight (Translation.trᴮ (Mx.miximalOf τ)) (Translation.trᴮ z))
      λ u hu → PT.rec
        (snd (u ≤ᴮ weight (Translation.trᴮ (Mx.miximalOf τ)) (Translation.trᴮ z)))
        (λ { (p , inner) → PT.rec
          (snd (u ≤ᴮ weight (Translation.trᴮ (Mx.miximalOf τ)) (Translation.trᴮ z)))
          (λ { (hp , heq) →
            subst (λ v → ⟨ v ≤ᴮ weight (Translation.trᴮ (Mx.miximalOf τ))
                              (Translation.trᴮ z) ⟩)
              (sym (Pt≡ {B} {u}
                {Base.iᴷ (p , inCar (BAT._∈ᴮ_ (Translation.trᴮ z) τ) p hp)}
                (≈→≡ heq)))
              (weight-principal τ z p
                (inCar (BAT._∈ᴮ_ (Translation.trᴮ z) τ) p hp)
                (subst (λ e → ⟨ e ∈ˢ Mx.miximalOf τ ⟩)
                  (sym (entry-agrees z p))
                  (Mx.miximal-entry τ z p hz hp))) })
          inner })
        (subst ⟨_⟩ (image-spec
          (fst (BAT._∈ᴮ_ (Translation.trᴮ z) τ))
          (λ q → fst (Base.iᴷ (fst q ,
            inCar (BAT._∈ᴮ_ (Translation.trᴮ z) τ) (fst q) (snd q))))
          (fst u)) hu))

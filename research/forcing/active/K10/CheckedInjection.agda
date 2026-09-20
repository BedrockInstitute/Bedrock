{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile
import CardinalBridge

module K10.CheckedInjection
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (families : NameKernel.Families 𝒮)
  (accessible : NameKernel.Accessibility 𝒮)
  (images : NameKernel.MemberImage 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (κ w : ZFStructure.S 𝒮)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.LevyHierarchy using ( Δ₀; checkΔ₀ )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Unit using ( tt )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )
import K7.CardinalOrder
import K9.NameGround
import K9.PairNames

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

module CBᴳ = CardinalBridge 𝒮
module NG = K9.NameGround 𝒮 families accessible images pow κ w
  using ( module GS; module K; module C; module P; module PS; module AtGeneric
        ; extensional; hasPair; ≈ˢ-paths )
module Pair = K9.PairNames 𝒮 families accessible images pow κ w
  using ( pairCode; pair-spec; pairNm )

private
  memLᴳ : (x y z : S) → ⟨ x ≈ˢ y ⟩ → (x ∈ˢ z) ≡ (y ∈ˢ z)
  memLᴳ x y z e = cong (λ u → u ∈ˢ z) (NG.GS.≈→≡ e)

  memRᴳ : (x y z : S) → ⟨ y ≈ˢ z ⟩ → (x ∈ˢ y) ≡ (x ∈ˢ z)
  memRᴳ x y z e = cong (x ∈ˢ_) (NG.GS.≈→≡ e)

  module COᴳ = K7.CardinalOrder 𝒮
  module Orderᴳ = COᴳ.Order NG.extensional memLᴳ memRᴳ

Δ₀-IsSingletonφ : Δ₀ CBᴳ.IsSingletonφ
Δ₀-IsSingletonφ = checkΔ₀ CBᴳ.IsSingletonφ tt

Δ₀-IsPairφ : Δ₀ CBᴳ.IsPairφ
Δ₀-IsPairφ = checkΔ₀ CBᴳ.IsPairφ tt

module AtGeneric
  (G : NG.P.Sub)
  (positive : ⟨ NG.P.positive G ⟩)
  where

  module Ground = NG.AtGeneric G
  module E = Ground.E
  module CopyBase = Ground.Copy
  module Copy = CopyBase.WithPos positive
  module CBᴱ = CardinalBridge NG.PS.𝒮ᴾ[ G ]

  open hPropStructure NG.PS.𝒮ᴾ[ G ]
    using () renaming ( _≈ˢ_ to _≈ᴱ_; _∈ˢ_ to _∈ᴱ_ )

  checked : S → NG.PS.Nameᴾ
  checked = CopyBase.groundName

  private
    module K = NG.K

    memLᴱ : (x y z : NG.PS.Nameᴾ) → ⟨ x ≈ᴱ y ⟩
          → (x ∈ᴱ z) ≡ (y ∈ᴱ z)
    memLᴱ x y z e = ⇔toPath
      (E.∈-congˡ e) (E.∈-congˡ (E.≈-sym e))

    memRᴱ : (x y z : NG.PS.Nameᴾ) → ⟨ y ≈ᴱ z ⟩
          → (x ∈ᴱ y) ≡ (x ∈ᴱ z)
    memRᴱ x y z e = ⇔toPath
      (E.∈-congʳ e) (E.∈-congʳ (E.≈-sym e))

    module COᴱ = K7.CardinalOrder NG.PS.𝒮ᴾ[ G ]
    module Orderᴱ = COᴱ.Order (NG.PS.P.Ext.extensional G) memLᴱ memRᴱ

  copy-mem : (a b : S) → ⟨ a ∈ˢ b ⟩ → ⟨ checked a ∈ᴱ checked b ⟩
  copy-mem a b h = subst ⟨_⟩ (sym (Copy.check-faithful a b)) h

  copy-eq : (a b : S) → ⟨ a ≈ˢ b ⟩ → ⟨ checked a ≈ᴱ checked b ⟩
  copy-eq a b h = subst ⟨_⟩ (sym (Copy.chk-≈ a b)) h

  checked-singleton : (t x : S) → ⟨ CBᴳ.isSingleton t x ⟩
                    → ⟨ CBᴱ.isSingleton (checked t) (checked x) ⟩
  checked-singleton t x h =
    subst ⟨_⟩ (CBᴱ.IsSingleton-bridge (checked t) (checked x))
      (subst ⟨_⟩
        (sym (Copy.groundSat CBᴳ.IsSingletonφ Δ₀-IsSingletonφ (t ∷ x ∷ [])))
        (subst ⟨_⟩ (sym (CBᴳ.IsSingleton-bridge t x)) h))

  checked-pair : (t x y : S) → ⟨ CBᴳ.isPair t x y ⟩
               → ⟨ CBᴱ.isPair (checked t) (checked x) (checked y) ⟩
  checked-pair t x y h =
    subst ⟨_⟩ (CBᴱ.IsPair-bridge (checked t) (checked x) (checked y))
      (subst ⟨_⟩
        (sym (Copy.groundSat CBᴳ.IsPairφ Δ₀-IsPairφ (t ∷ x ∷ y ∷ [])))
        (subst ⟨_⟩ (sym (CBᴳ.IsPair-bridge t x y)) h))

  private
    pair-value : (m n z : S) → (z E.∈[G] Pair.pairCode m n)
               ≡ ((z E.≈[G] m) ⊔ (z E.≈[G] n))
    pair-value m n z = ⇔toPath forward backward
      where
      target : Ω
      target = (z E.≈[G] m) ⊔ (z E.≈[G] n)

      forward : ⟨ z E.∈[G] Pair.pairCode m n ⟩ → ⟨ target ⟩
      forward hz = PT.rec (snd target)
        (λ { (y , hy , zy) → PT.rec (snd target)
          (λ { (p , hp , member , hG) → PT.rec (snd target)
            (λ { (inl hm) → PT.map
                    (λ { (q , hq , eq) → inl (subst (λ x → ⟨ z E.≈[G] x ⟩)
                      (K.entry-inj (NG.GS.≈→≡ eq) .fst) zy) }) hm
               ; (inr hn) → PT.map
                    (λ { (q , hq , eq) → inr (subst (λ x → ⟨ z E.≈[G] x ⟩)
                      (K.entry-inj (NG.GS.≈→≡ eq) .fst) zy) }) hn })
            (subst ⟨_⟩ (Pair.pair-spec m n (K.entry y p)) member) }) hy }) hz

      backward : ⟨ target ⟩ → ⟨ z E.∈[G] Pair.pairCode m n ⟩
      backward h = PT.rec (snd (z E.∈[G] Pair.pairCode m n))
        (λ { ((p , hp) , hG) → PT.rec (snd (z E.∈[G] Pair.pairCode m n))
          (λ { (inl zm) → E.∈-congˡ (E.≈-sym zm)
                  (E.entry-value (Pair.pairCode m n) m p hp hG
                    (subst ⟨_⟩ (sym (Pair.pair-spec m n (K.entry m p)))
                      ∣ inl ∣ p , hp , subst ⟨_⟩
                        (sym (NG.≈ˢ-paths (K.entry m p) (K.entry m p))) refl ∣₁ ∣₁))
             ; (inr zn) → E.∈-congˡ (E.≈-sym zn)
                  (E.entry-value (Pair.pairCode m n) n p hp hG
                    (subst ⟨_⟩ (sym (Pair.pair-spec m n (K.entry n p)))
                      ∣ inr ∣ p , hp , subst ⟨_⟩
                        (sym (NG.≈ˢ-paths (K.entry n p) (K.entry n p))) refl ∣₁ ∣₁)) }) h })
        positive

    extensionPairing : OrdinaryProfile.Pairing NG.PS.𝒮ᴾ[ G ]
    extensionPairing σ τ = ∣ Pair.pairNm σ τ , (λ ρ →
        subst ⟨_⟩ (pair-value (fst σ) (fst τ) (fst ρ))
      , subst ⟨_⟩ (sym (pair-value (fst σ) (fst τ) (fst ρ)))) ∣₁

    kpair-cong : (q p x y : NG.PS.Nameᴾ) → ⟨ q ≈ᴱ p ⟩
               → ⟨ CBᴱ.isKPair p x y ⟩ → ⟨ CBᴱ.isKPair q x y ⟩
    kpair-cong q p x y eq hp t =
        (λ ht → hp t .fst (E.∈-congʳ eq ht))
      , (λ shape → E.∈-congʳ (E.≈-sym eq) (hp t .snd shape))

  checked-kpair : (p x y : S) → ⟨ CBᴳ.isKPair p x y ⟩
                → ⟨ CBᴱ.isKPair (checked p) (checked x) (checked y) ⟩
  checked-kpair p x y hp t = forward , backward
    where
    target : Ω
    target = CBᴱ.isSingleton t (checked x) ⊔ CBᴱ.isPair t (checked x) (checked y)

    forward : ⟨ t ∈ᴱ checked p ⟩ → ⟨ target ⟩
    forward ht = PT.rec (snd target)
      (λ { (u , hu , eq) → PT.map
        (λ { (inl hs) → inl (Orderᴱ.sgl-cong t (checked u) (checked x) eq
                                (checked-singleton u x hs))
           ; (inr hr) → inr (Orderᴱ.pr-cong t (checked u) (checked x) (checked y) eq
                                (checked-pair u x y hr)) })
        (hp u .fst hu) })
      (subst ⟨_⟩ (Copy.check-value p (fst t)) ht)

    backward : ⟨ target ⟩ → ⟨ t ∈ᴱ checked p ⟩
    backward = PT.rec (snd (t ∈ᴱ checked p)) choose
      where
      choose : ⟨ CBᴱ.isSingleton t (checked x) ⟩
             ⊎ ⟨ CBᴱ.isPair t (checked x) (checked y) ⟩
             → ⟨ t ∈ᴱ checked p ⟩
      choose (inl hs) = PT.rec (snd (t ∈ᴱ checked p))
        (λ { (s , groundS) → E.∈-congˡ
          (E.≈-sym (Orderᴱ.sgl-unique t (checked s) (checked x) hs
            (checked-singleton s x groundS)))
          (copy-mem s p (hp s .snd ∣ inl groundS ∣₁)) })
        (Orderᴳ.sglOf NG.hasPair x)
      choose (inr hr) = PT.rec (snd (t ∈ᴱ checked p))
        (λ { (r , groundR) → E.∈-congˡ
          (E.≈-sym (Orderᴱ.pr-unique t (checked r) (checked x) (checked y) hr
            (checked-pair r x y groundR)))
          (copy-mem r p (hp r .snd ∣ inr groundR ∣₁)) })
        (Orderᴳ.prOf NG.hasPair x y)

  private
    components : (p x y : S) → ⟨ CBᴳ.isKPair p x y ⟩
               → (q u v : NG.PS.Nameᴾ) → ⟨ q ≈ᴱ checked p ⟩
               → ⟨ CBᴱ.isKPair q u v ⟩
               → ⟨ (checked x ≈ᴱ u) ⊓ (checked y ≈ᴱ v) ⟩
    components p x y hp q u v eq hq =
      Orderᴱ.kpair-components extensionPairing (checked p) (checked x) (checked y) u v
        (checked-kpair p x y hp)
        (kpair-cong (checked p) q u v (E.≈-sym eq) hq)

  checked-isInjection : (f a b : S) → ⟨ CBᴳ.isInjection f a b ⟩
                      → ⟨ CBᴱ.isInjection (checked f) (checked a) (checked b) ⟩
  checked-isInjection f a b hf =
      (relation , single-valued)
    , domain-total
    , range-in
    , injective
    where
    View : NG.PS.Nameᴾ → Type ℓ
    View q = Σ[ p ∈ S ] Σ[ x ∈ S ] Σ[ y ∈ S ]
      (⟨ p ∈ˢ f ⟩ × (⟨ q ≈ᴱ checked p ⟩ × ⟨ CBᴳ.isKPair p x y ⟩))

    view : (q : NG.PS.Nameᴾ) → ⟨ q ∈ᴱ checked f ⟩ → ∥ View q ∥₁
    view q hq = PT.rec PT.squash₁
      (λ { (p , hp , eq) → PT.rec PT.squash₁
        (λ { (x , pairs) → PT.map
          (λ { (y , pairP) → p , x , y , hp , eq , pairP }) pairs })
        (hf .fst .fst p hp) })
      (subst ⟨_⟩ (Copy.check-value f (fst q)) hq)

    relation : ⟨ CBᴱ.isRelation (checked f) ⟩
    relation q hq = PT.map
      (λ { (p , x , y , hp , eq , pairP) → checked x
        , ∣ checked y
          , kpair-cong q (checked p) (checked x) (checked y) eq
              (checked-kpair p x y pairP) ∣₁ })
      (view q hq)

    single-valued : (p : NG.PS.Nameᴾ) → ⟨ p ∈ᴱ checked f ⟩
      → (q : NG.PS.Nameᴾ) → ⟨ q ∈ᴱ checked f ⟩
      → (x y z : NG.PS.Nameᴾ)
      → ⟨ (CBᴱ.isKPair p x y) ⊓ (CBᴱ.isKPair q x z) ⟩
      → ⟨ y ≈ᴱ z ⟩
    single-valued p hp q hq x y z (pairP , pairQ) =
      PT.rec (snd (y ≈ᴱ z)) atP (view p hp)
      where
      atP : View p → ⟨ y ≈ᴱ z ⟩
      atP (p₀ , x₀ , y₀ , hp₀ , ep , groundP) =
        PT.rec (snd (y ≈ᴱ z)) atQ (view q hq)
        where
        cp = components p₀ x₀ y₀ groundP p x y ep pairP

        atQ : View q → ⟨ y ≈ᴱ z ⟩
        atQ (q₀ , x₁ , z₀ , hq₀ , eq , groundQ) =
          E.≈-trans (E.≈-sym (cp .snd))
            (E.≈-trans (copy-eq y₀ z₀ groundResult) (cq .snd))
          where
          cq = components q₀ x₁ z₀ groundQ q x z eq pairQ
          firstEq : ⟨ x₀ ≈ˢ x₁ ⟩
          firstEq = Copy.check-≈-inj x₀ x₁
            (E.≈-trans (cp .fst) (E.≈-sym (cq .fst)))
          groundResult : ⟨ y₀ ≈ˢ z₀ ⟩
          groundResult = hf .fst .snd p₀ hp₀ q₀ hq₀ x₁ y₀ z₀
            (Orderᴳ.kpair-subst p₀ x₀ x₁ y₀ y₀ firstEq
              (Orderᴳ.≈-refl y₀) groundP , groundQ)

    domain-total : (x : NG.PS.Nameᴾ) → ⟨ x ∈ᴱ checked a ⟩
      → ⟨ ⋁ NG.PS.Nameᴾ (λ y → ⋁ NG.PS.Nameᴾ (λ p →
        (p ∈ᴱ checked f) ⊓ CBᴱ.isKPair p x y)) ⟩
    domain-total x hx = PT.rec PT.squash₁ atX
      (subst ⟨_⟩ (Copy.check-value a (fst x)) hx)
      where
      atX : Σ[ x₀ ∈ S ] (⟨ x₀ ∈ˢ a ⟩ × ⟨ x ≈ᴱ checked x₀ ⟩)
          → ⟨ ⋁ NG.PS.Nameᴾ (λ y → ⋁ NG.PS.Nameᴾ (λ p →
              (p ∈ᴱ checked f) ⊓ CBᴱ.isKPair p x y)) ⟩
      atX (x₀ , hx₀ , ex) = PT.map
        (λ { (y₀ , pairs) → checked y₀ , PT.map
          (λ { (p₀ , hp₀ , pairP) → checked p₀
            , copy-mem p₀ f hp₀
            , Orderᴱ.kpair-subst (checked p₀) (checked x₀) x
                (checked y₀) (checked y₀) (E.≈-sym ex) (E.≈-refl (fst (checked y₀)))
                (checked-kpair p₀ x₀ y₀ pairP) }) pairs })
        (hf .snd .fst x₀ hx₀)

    range-in : (p : NG.PS.Nameᴾ) → ⟨ p ∈ᴱ checked f ⟩
      → (x y : NG.PS.Nameᴾ) → ⟨ CBᴱ.isKPair p x y ⟩
      → ⟨ y ∈ᴱ checked b ⟩
    range-in p hp x y pairP = PT.rec (snd (y ∈ᴱ checked b)) atP (view p hp)
      where
      atP : View p → ⟨ y ∈ᴱ checked b ⟩
      atP (p₀ , x₀ , y₀ , hp₀ , ep , groundP) = E.∈-congˡ (cp .snd)
        (copy-mem y₀ b (hf .snd .snd .fst p₀ hp₀ x₀ y₀ groundP))
        where
        cp = components p₀ x₀ y₀ groundP p x y ep pairP

    injective : (p : NG.PS.Nameᴾ) → ⟨ p ∈ᴱ checked f ⟩
      → (q : NG.PS.Nameᴾ) → ⟨ q ∈ᴱ checked f ⟩
      → (x y z : NG.PS.Nameᴾ)
      → ⟨ (CBᴱ.isKPair p x y) ⊓ (CBᴱ.isKPair q z y) ⟩
      → ⟨ x ≈ᴱ z ⟩
    injective p hp q hq x y z (pairP , pairQ) =
      PT.rec (snd (x ≈ᴱ z)) atP (view p hp)
      where
      atP : View p → ⟨ x ≈ᴱ z ⟩
      atP (p₀ , x₀ , y₀ , hp₀ , ep , groundP) =
        PT.rec (snd (x ≈ᴱ z)) atQ (view q hq)
        where
        cp = components p₀ x₀ y₀ groundP p x y ep pairP

        atQ : View q → ⟨ x ≈ᴱ z ⟩
        atQ (q₀ , z₀ , y₁ , hq₀ , eq , groundQ) =
          E.≈-trans (E.≈-sym (cp .fst))
            (E.≈-trans (copy-eq x₀ z₀ groundResult) (cq .fst))
          where
          cq = components q₀ z₀ y₁ groundQ q z y eq pairQ
          secondEq : ⟨ y₀ ≈ˢ y₁ ⟩
          secondEq = Copy.check-≈-inj y₀ y₁
            (E.≈-trans (cp .snd) (E.≈-sym (cq .snd)))
          groundResult : ⟨ x₀ ≈ˢ z₀ ⟩
          groundResult = hf .snd .snd .snd p₀ hp₀ q₀ hq₀ x₀ y₁ z₀
            (Orderᴳ.kpair-subst p₀ x₀ x₀ y₀ y₁ (Orderᴳ.≈-refl x₀)
              secondEq groundP , groundQ)

  checked-injectable : (a b : S) → ⟨ CBᴳ.injectable a b ⟩
                     → ⟨ CBᴱ.injectable (checked a) (checked b) ⟩
  checked-injectable a b = PT.map
    (λ { (f , hf) → checked f , checked-isInjection f a b hf })

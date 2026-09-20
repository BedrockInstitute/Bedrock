{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )

module K8.GroundSets {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _∈̇_; ⊥̇; ∃̇∈ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
open import OrdinaryProfile 𝒮 using
  ( iff; Extensionality; Pairing; Union; PowerSet; Separation )
import GroundDescription
import NameKernel
import NameSupport
import K7.CardinalOrder
import CardinalBridge
open import CodedVocabulary 𝒮 using
  ( isSglΔ; isPairΔ; isKPairΔ; prAtˢ; subsetΔ; sepAt; sepAt-reading )
open import Cubical.Data.Sum using ( inl; inr )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )

module Ground
  (ext   : Extensionality)
  (paths : (x y : S) → (x ≈ˢ y) ≡ ((x ≡ y) , isSetS x y))
  (pair  : Pairing)
  (un    : Union)
  (pow   : PowerSet)
  (sep   : Separation)
  (seed  : S) where

  module GD = GroundDescription 𝒮 ext paths
  open GD using ( the; the-spec; powerOf; powerOf-spec; separateOf; separateOf-spec )

  core : NameKernel.Core 𝒮
  core = record { extensional = ext ; hasPair = pair ; ≈ˢ-paths = paths }

  module Det = NameSupport.Determinacy 𝒮 core

  ≈→≡ : {x y : S} → ⟨ x ≈ˢ y ⟩ → x ≡ y
  ≈→≡ {x} {y} = subst ⟨_⟩ (paths x y)

  private
    pairClass : S → S → S → Ω
    pairClass a b x = (x ≈ˢ a) ⊔ (x ≈ˢ b)

  opaque
    pairOf : S → S → S
    pairOf a b = the (pairClass a b) (pair a b)

    pairOf-spec : (a b x : S) → (x ∈ˢ pairOf a b) ≡ pairClass a b x
    pairOf-spec a b = the-spec (pairClass a b) (pair a b)

  pairOf-inˡ : (a b : S) → ⟨ a ∈ˢ pairOf a b ⟩
  pairOf-inˡ a b = subst ⟨_⟩ (sym (pairOf-spec a b a)) ∣ inl (subst ⟨_⟩ (sym (paths a a)) refl) ∣₁

  pairOf-inʳ : (a b : S) → ⟨ b ∈ˢ pairOf a b ⟩
  pairOf-inʳ a b = subst ⟨_⟩ (sym (pairOf-spec a b b)) ∣ inr (subst ⟨_⟩ (sym (paths b b)) refl) ∣₁

  pairOf-out : (a b x : S) → ⟨ x ∈ˢ pairOf a b ⟩ → ⟨ (x ≈ˢ a) ⊔ (x ≈ˢ b) ⟩
  pairOf-out a b x = subst ⟨_⟩ (pairOf-spec a b x)

  singleton : S → S
  singleton a = pairOf a a

  singleton-witness : (a : S) → ⟨ isSglΔ (singleton a) a ⟩
  singleton-witness a = pairOf-inˡ a a , λ x hx →
    PT.rec (snd (x ≈ˢ a)) (λ { (inl h) → h ; (inr h) → h }) (pairOf-out a a x hx)

  pair-witness : (a b : S) → ⟨ isPairΔ (pairOf a b) a b ⟩
  pair-witness a b = pairOf-inˡ a b , pairOf-inʳ a b , pairOf-out a b

  empty : S
  empty = separateOf sep seed ⊥̇

  empty-out : (x : S) → ⟨ x ∈ˢ empty ⟩ → ⟨ ⊥ ⟩
  empty-out x h = subst ⟨_⟩ (separateOf-spec sep seed ⊥̇ x) h .snd

  private
    unionClass : S → S → Ω
    unionClass a x = ⋁ S (λ y → (y ∈ˢ a) ⊓ (x ∈ˢ y))

    unionOf : S → S
    unionOf a = the (unionClass a) (un a)

    unionOf-spec : (a x : S) → (x ∈ˢ unionOf a) ≡ unionClass a x
    unionOf-spec a = the-spec (unionClass a) (un a)

  opaque
    join : S → S → S
    join a b = unionOf (pairOf a b)

    join-spec : (a b x : S) → (x ∈ˢ join a b) ≡ ((x ∈ˢ a) ⊔ (x ∈ˢ b))
    join-spec a b x = ⇔toPath forward backward
      where
      forward : ⟨ x ∈ˢ join a b ⟩ → ⟨ (x ∈ˢ a) ⊔ (x ∈ˢ b) ⟩
      forward h = PT.rec (snd ((x ∈ˢ a) ⊔ (x ∈ˢ b))) step
        (subst ⟨_⟩ (unionOf-spec (pairOf a b) x) h)
        where
        step : Σ[ y ∈ S ] (⟨ y ∈ˢ pairOf a b ⟩ × ⟨ x ∈ˢ y ⟩)
             → ⟨ (x ∈ˢ a) ⊔ (x ∈ˢ b) ⟩
        step (y , hy , hx) = PT.rec (snd ((x ∈ˢ a) ⊔ (x ∈ˢ b)))
          (λ { (inl e) → ∣ inl (subst (λ z → ⟨ x ∈ˢ z ⟩) (≈→≡ e) hx) ∣₁
             ; (inr e) → ∣ inr (subst (λ z → ⟨ x ∈ˢ z ⟩) (≈→≡ e) hx) ∣₁ })
          (pairOf-out a b y hy)
      backward : ⟨ (x ∈ˢ a) ⊔ (x ∈ˢ b) ⟩ → ⟨ x ∈ˢ join a b ⟩
      backward = PT.rec (snd (x ∈ˢ join a b)) λ
        { (inl h) → subst ⟨_⟩ (sym (unionOf-spec (pairOf a b) x)) ∣ a , pairOf-inˡ a b , h ∣₁
        ; (inr h) → subst ⟨_⟩ (sym (unionOf-spec (pairOf a b) x)) ∣ b , pairOf-inʳ a b , h ∣₁ }

  opaque
    power : S → S
    power = powerOf pow

    power-spec : (a x : S) → (x ∈ˢ power a) ≡ subsetΔ x a
    power-spec = powerOf-spec pow

  separator : S → Formula S 1 → S
  separator = separateOf sep

  separator-spec : (a : S) (φ : Formula S 1) (x : S)
                 → (x ∈ˢ separator a φ) ≡ ((x ∈ˢ a) ⊓ ((x ∷ []) ⊨ φ))
  separator-spec = separateOf-spec sep

  ordered : S → S → S
  ordered a b = pairOf (singleton a) (pairOf a b)

  ordered-witness : (a b : S) → ⟨ isKPairΔ (ordered a b) a b ⟩
  ordered-witness a b =
      ∣ singleton a , pairOf-inˡ (singleton a) (pairOf a b) , singleton-witness a ∣₁
    , (∣ pairOf a b , pairOf-inʳ (singleton a) (pairOf a b) , pair-witness a b ∣₁
    , λ w hw → PT.map
        (λ { (inl e) → inl (subst (λ z → ⟨ isSglΔ z a ⟩) (sym (≈→≡ e)) (singleton-witness a))
           ; (inr e) → inr (subst (λ z → ⟨ isPairΔ z a b ⟩) (sym (≈→≡ e)) (pair-witness a b)) })
        (pairOf-out (singleton a) (pairOf a b) w hw))

  ordered-unique : (p a b : S) → ⟨ isKPairΔ p a b ⟩ → p ≡ ordered a b
  ordered-unique p a b h = Det.kpair-det p (ordered a b) a b h (ordered-witness a b)

  private
    module CB = CardinalBridge 𝒮

    delta→kpair : (p a b : S) → ⟨ isKPairΔ p a b ⟩ → ⟨ CB.isKPair p a b ⟩
    delta→kpair p a b h t = h .snd .snd t , back
      where
      back : ⟨ (CB.isSingleton t a) ⊔ (CB.isPair t a b) ⟩ → ⟨ t ∈ˢ p ⟩
      back = PT.rec (snd (t ∈ˢ p)) λ
        { (inl hs) → PT.rec (snd (t ∈ˢ p))
            (λ { (s , hs∈p , hsa) →
              subst (λ z → ⟨ z ∈ˢ p ⟩) (sym (Det.sgl-det t s a hs hsa)) hs∈p })
            (h .fst)
        ; (inr hp) → PT.rec (snd (t ∈ˢ p))
            (λ { (q , hq∈p , hqab) →
              subst (λ z → ⟨ z ∈ˢ p ⟩) (sym (Det.pair-det t q a b hp hqab)) hq∈p })
            (h .snd .fst) }

  ordered-components : (p a b a' b' : S)
                     → ⟨ isKPairΔ p a b ⟩ → ⟨ isKPairΔ p a' b' ⟩
                     → (a ≡ a') × (b ≡ b')
  ordered-components p a b a' b' h h' =
    ordered-inj (sym (ordered-unique p a b h) ∙ ordered-unique p a' b' h')
    where
    ordered-inj : ordered a b ≡ ordered a' b' → (a ≡ a') × (b ≡ b')
    ordered-inj q =
      ≈→≡ (fst (components q)) , ≈→≡ (snd (components q))
      where
      module CO = K7.CardinalOrder.Order 𝒮 ext
        (λ x y z e → cong (_∈ˢ z) (≈→≡ e))
        (λ x y z e → cong (x ∈ˢ_) (≈→≡ e))
      components : ordered a b ≡ ordered a' b' → ⟨ (a ≈ˢ a') ⊓ (b ≈ˢ b') ⟩
      components q = CO.kpair-components pair (ordered a' b') a b a' b'
        (delta→kpair (ordered a' b') a b
          (subst (λ z → ⟨ isKPairΔ z a b ⟩) q (ordered-witness a b)))
        (delta→kpair (ordered a' b') a' b' (ordered-witness a' b'))

  private
    prodBound : S → S → S
    prodBound a b = power (power (join a b))

    prodFo : (a b : S) → Formula S 1
    prodFo a b = ∃̇∈ (con a) (∃̇∈ (con b) (prAtˢ (suc (suc zero)) (suc zero) zero))

  opaque
    product : S → S → S
    product a b = separator (prodBound a b) (prodFo a b)

    product-out : (a b p : S) → ⟨ p ∈ˢ product a b ⟩
                → ∥ Σ[ x ∈ S ] Σ[ y ∈ S ]
                     (⟨ x ∈ˢ a ⟩ × ⟨ y ∈ˢ b ⟩ × ⟨ isKPairΔ p x y ⟩) ∥₁
    product-out a b p h = PT.rec PT.squash₁
      (λ { (x , hx , rest) → PT.rec PT.squash₁
        (λ { (y , hy , hp) → ∣ x , y , hx , hy , hp ∣₁ }) rest })
      (subst ⟨_⟩ (sepAt-reading (prodFo a b) [] p)
        (subst ⟨_⟩ (separator-spec (prodBound a b) (prodFo a b) p) h .snd))

    product-in : (a b x y : S) → ⟨ x ∈ˢ a ⟩ → ⟨ y ∈ˢ b ⟩
               → ⟨ ordered x y ∈ˢ product a b ⟩
    product-in a b x y hx hy = subst ⟨_⟩
      (sym (separator-spec (prodBound a b) (prodFo a b) (ordered x y)))
      ( inBound
      , subst ⟨_⟩ (sym (sepAt-reading (prodFo a b) [] (ordered x y)))
          ∣ x , hx , ∣ y , hy , ordered-witness x y ∣₁ ∣₁ )
      where
      xsub : ⟨ subsetΔ (singleton x) (join a b) ⟩
      xsub z hz = subst ⟨_⟩ (sym (join-spec a b z))
        ∣ inl (subst (λ t → ⟨ t ∈ˢ a ⟩) (sym (≈→≡ (singleton-witness x .snd z hz))) hx) ∣₁
      xysub : ⟨ subsetΔ (pairOf x y) (join a b) ⟩
      xysub z hz = PT.rec (snd (z ∈ˢ join a b))
        (λ { (inl e) → subst ⟨_⟩ (sym (join-spec a b z))
               ∣ inl (subst (λ t → ⟨ t ∈ˢ a ⟩) (sym (≈→≡ e)) hx) ∣₁
           ; (inr e) → subst ⟨_⟩ (sym (join-spec a b z))
               ∣ inr (subst (λ t → ⟨ t ∈ˢ b ⟩) (sym (≈→≡ e)) hy) ∣₁ })
        (pairOf-out x y z hz)
      sIn : ⟨ singleton x ∈ˢ power (join a b) ⟩
      sIn = subst ⟨_⟩ (sym (power-spec (join a b) (singleton x))) xsub
      xyIn : ⟨ pairOf x y ∈ˢ power (join a b) ⟩
      xyIn = subst ⟨_⟩ (sym (power-spec (join a b) (pairOf x y))) xysub
      ordSub : ⟨ subsetΔ (ordered x y) (power (join a b)) ⟩
      ordSub z hz = PT.rec (snd (z ∈ˢ power (join a b)))
        (λ { (inl e) → subst (λ t → ⟨ t ∈ˢ power (join a b) ⟩) (sym (≈→≡ e)) sIn
           ; (inr e) → subst (λ t → ⟨ t ∈ˢ power (join a b) ⟩) (sym (≈→≡ e)) xyIn })
        (pairOf-out (singleton x) (pairOf x y) z hz)
      inBound : ⟨ ordered x y ∈ˢ prodBound a b ⟩
      inBound = subst ⟨_⟩ (sym (power-spec (power (join a b)) (ordered x y))) ordSub

{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile

module K8.OmegaFinite
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext   : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
    → ZFStructure._≈ˢ_ 𝒮 x y ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  (pair  : OrdinaryProfile.Pairing 𝒮)
  (un    : OrdinaryProfile.Union 𝒮)
  (pow   : OrdinaryProfile.PowerSet 𝒮)
  (sep   : OrdinaryProfile.Separation 𝒮)
  (find  : OrdinaryProfile.FoundationInduction 𝒮)
  (seed  : ZFStructure.S 𝒮)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; var; con; _∈̇_; _≐_; _∨̇_; ∀̇∈; ∃̇∈ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
import CardinalBridge
import K7.CardinalOrder
import K8.GroundSets
open import K8.FiniteVocabulary 𝒮
  using ( finiteIn; emptyPred; adjoinPred )
open import K8.FiniteSets 𝒮 ext paths pow sep using ( finite-induction )
open import Cubical.Data.Sum using ( _⊎_ ) renaming ( inl to inl⊎; inr to inr⊎ )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )

module CB = CardinalBridge 𝒮
module GS = K8.GroundSets.Ground 𝒮 ext paths pair un pow sep seed
open GS using ( separator; separator-spec; ≈→≡ )

module CO = K7.CardinalOrder.Order 𝒮 ext
  (λ x y z e → cong (_∈ˢ z) (≈→≡ e))
  (λ x y z e → cong (x ∈ˢ_) (≈→≡ e))

≈-refl : (x : S) → ⟨ x ≈ˢ x ⟩
≈-refl x = subst ⟨_⟩ (sym (paths x x)) refl

empty-ordinal : (e : S) → ⟨ emptyPred e ⟩ → ⟨ CB.isOrdinal e ⟩
empty-ordinal e he = transitive , linear
  where
  transitive : ⟨ CB.isTransitiveSet e ⟩
  transitive x hx = Empty.rec* (he x hx)

  linear : ⟨ ⋀ S (λ x → (x ∈ˢ e) ⇒ ⋀ S (λ y → (y ∈ˢ e) ⇒
    ((x ∈ˢ y) ⊔ ((x ≈ˢ y) ⊔ (y ∈ˢ x))))) ⟩
  linear x hx = Empty.rec* (he x hx)

successor-ordinal : (n s : S) → ⟨ CB.isOrdinal n ⟩
  → ⟨ CB.isSuccOf s n ⟩ → ⟨ CB.isOrdinal s ⟩
successor-ordinal n s hn hs = transitive , linear
  where
  n⊆s : (z : S) → ⟨ z ∈ˢ n ⟩ → ⟨ z ∈ˢ s ⟩
  n⊆s = hs .snd .fst

  out : (z : S) → ⟨ z ∈ˢ s ⟩ → ⟨ (z ∈ˢ n) ⊔ (z ≈ˢ n) ⟩
  out = hs .snd .snd

  transitive : ⟨ CB.isTransitiveSet s ⟩
  transitive x hx y hy = PT.rec (snd (y ∈ˢ s)) step (out x hx)
    where
    step : ⟨ x ∈ˢ n ⟩ ⊎ ⟨ x ≈ˢ n ⟩ → ⟨ y ∈ˢ s ⟩
    step (inl⊎ xin) = n⊆s y (hn .fst x xin y hy)
    step (inr⊎ xeq) = n⊆s y
      (subst (λ z → ⟨ y ∈ˢ z ⟩) (≈→≡ xeq) hy)

  linear : ⟨ ⋀ S (λ x → (x ∈ˢ s) ⇒ ⋀ S (λ y → (y ∈ˢ s) ⇒
    ((x ∈ˢ y) ⊔ ((x ≈ˢ y) ⊔ (y ∈ˢ x))))) ⟩
  linear x hx y hy = PT.rec (snd goal) first (out x hx)
    where
    goal : Ω
    goal = (x ∈ˢ y) ⊔ ((x ≈ˢ y) ⊔ (y ∈ˢ x))

    first : ⟨ x ∈ˢ n ⟩ ⊎ ⟨ x ≈ˢ n ⟩ → ⟨ goal ⟩
    first (inl⊎ xin) = PT.rec (snd goal)
      (λ { (inl⊎ yin) → hn .snd x xin y yin
         ; (inr⊎ yeq) → ∣ inl⊎ (subst (λ z → ⟨ x ∈ˢ z ⟩) (sym (≈→≡ yeq)) xin) ∣₁ })
      (out y hy)
    first (inr⊎ xeq) = PT.rec (snd goal)
      (λ { (inl⊎ yin) → ∣ inr⊎ ∣ inr⊎
            (subst (λ z → ⟨ y ∈ˢ z ⟩) (sym (≈→≡ xeq)) yin) ∣₁ ∣₁
         ; (inr⊎ yeq) → ∣ inr⊎ ∣ inl⊎
            (subst (λ z → ⟨ x ≈ˢ z ⟩) (sym (≈→≡ yeq)) xeq) ∣₁ ∣₁ })
      (out y hy)

omega-members-ordinal : (w : S) → ⟨ CB.isOmega w ⟩
  → (n : S) → ⟨ n ∈ˢ w ⟩ → ⟨ CB.isOrdinal n ⟩
omega-members-ordinal w hw n hn = ordinal-part
  where
  ordinals : S
  ordinals = separator w CB.IsOrdinalφ

  ordinals-spec : (x : S)
    → (x ∈ˢ ordinals) ≡ ((x ∈ˢ w) ⊓ CB.isOrdinal x)
  ordinals-spec x = separator-spec w CB.IsOrdinalφ x
    ∙ cong ((x ∈ˢ w) ⊓_) (CB.IsOrdinal-bridge x)

  ordinals-inductive : ⟨ CB.isInductive ordinals ⟩
  ordinals-inductive = empty-member , successor-closed
    where
    empty-member : ⟨ ⋁ S (λ e → (e ∈ˢ ordinals) ⊓ emptyPred e) ⟩
    empty-member = PT.map
      (λ { (e , hew , he) → e ,
        subst ⟨_⟩ (sym (ordinals-spec e)) (hew , empty-ordinal e he) , he })
      (hw .fst .fst)

    successor-closed : ⟨ ⋀ S (λ x → (x ∈ˢ ordinals) ⇒
      ⋁ S (λ y → (y ∈ˢ ordinals) ⊓ CB.isSuccOf y x)) ⟩
    successor-closed x hx = PT.map
      (λ { (y , hyw , hsucc) → y ,
        subst ⟨_⟩ (sym (ordinals-spec y))
          (hyw , successor-ordinal x y (subst ⟨_⟩ (ordinals-spec x) hx .snd) hsucc)
        , hsucc })
      (hw .fst .snd x (subst ⟨_⟩ (ordinals-spec x) hx .fst))

  n-in : ⟨ n ∈ˢ ordinals ⟩
  n-in = hw .snd ordinals ordinals-inductive n hn

  ordinal-part : ⟨ CB.isOrdinal n ⟩
  ordinal-part = subst ⟨_⟩ (ordinals-spec n) n-in .snd

Bound : S → S → Ω
Bound w a = ⋁ S (λ n → (n ∈ˢ w) ⊓
  ⋀ S (λ x → (x ∈ˢ a) ⇒ ((x ∈ˢ n) ⊔ (x ≈ˢ n))))

boundAt : S → Formula S 1
boundAt w = ∃̇∈ (con w)
  (∀̇∈ (var (suc zero))
    ((var zero ∈̇ var (suc zero)) ∨̇ (var zero ≐ var (suc zero))))

bound-reading : (w a : S) → ((a ∷ []) ⊨ boundAt w) ≡ Bound w a
bound-reading w a = refl

finite-bound : LEM ℓ → (w : S) → ⟨ CB.isOmega w ⟩
  → (a : S) → ⟨ finiteIn w a ⟩ → ⟨ Bound w a ⟩
finite-bound lem w hw a ha = subst ⟨_⟩ (bound-reading w a)
  (finite-induction w (boundAt w) base step a ha)
  where
  base : (e : S) → ⟨ emptyPred e ⟩ → ⟨ (e ∷ []) ⊨ boundAt w ⟩
  base e he = subst ⟨_⟩ (sym (bound-reading w e))
    (PT.map (λ { (n , hn , _) → n , hn , λ x hx → Empty.rec* (he x hx) })
      (hw .fst .fst))

  step : (u b x : S) → ⟨ finiteIn w u ⟩ → ⟨ (u ∷ []) ⊨ boundAt w ⟩
    → ⟨ x ∈ˢ w ⟩ → ⟨ adjoinPred b u x ⟩ → ⟨ (b ∷ []) ⊨ boundAt w ⟩
  step u b x hu ih hx hb = subst ⟨_⟩ (sym (bound-reading w b))
    (PT.rec (snd (Bound w b)) extend (subst ⟨_⟩ (bound-reading w u) ih))
    where
    extend : Σ[ n ∈ S ] (⟨ n ∈ˢ w ⟩ ×
      ((z : S) → ⟨ z ∈ˢ u ⟩ → ⟨ (z ∈ˢ n) ⊔ (z ≈ˢ n) ⟩))
      → ⟨ Bound w b ⟩
    extend (n , hn , upper) = PT.rec (snd (Bound w b)) choose
      (CO.ord-compare find sep lem n x
        (omega-members-ordinal w hw n hn) (omega-members-ordinal w hw x hx))
      where
      choose : ⟨ n ∈ˢ x ⟩ ⊎ ⟨ (n ≈ˢ x) ⊔ (x ∈ˢ n) ⟩ → ⟨ Bound w b ⟩
      choose (inl⊎ n<x) = ∣ x , hx , upper-x ∣₁
        where
        upper-x : (z : S) → ⟨ z ∈ˢ b ⟩ → ⟨ (z ∈ˢ x) ⊔ (z ≈ˢ x) ⟩
        upper-x z hz = PT.rec (snd ((z ∈ˢ x) ⊔ (z ≈ˢ x))) from-adjoin
          (hb .snd .snd z hz)
          where
          from-adjoin : ⟨ z ∈ˢ u ⟩ ⊎ ⟨ z ≈ˢ x ⟩
            → ⟨ (z ∈ˢ x) ⊔ (z ≈ˢ x) ⟩
          from-adjoin (inr⊎ z=x) = ∣ inr⊎ z=x ∣₁
          from-adjoin (inl⊎ zu) = PT.rec (snd ((z ∈ˢ x) ⊔ (z ≈ˢ x)))
            (λ { (inl⊎ z<n) → ∣ inl⊎
                    ((omega-members-ordinal w hw x hx) .fst n n<x z z<n) ∣₁
               ; (inr⊎ z=n) → ∣ inl⊎
                    (subst (λ q → ⟨ q ∈ˢ x ⟩) (sym (≈→≡ z=n)) n<x) ∣₁ })
            (upper z zu)
      choose (inr⊎ rel) = PT.rec (snd (Bound w b)) keep-n rel
        where
        upper-n : (⟨ n ≈ˢ x ⟩ ⊎ ⟨ x ∈ˢ n ⟩)
          → (z : S) → ⟨ z ∈ˢ b ⟩ → ⟨ (z ∈ˢ n) ⊔ (z ≈ˢ n) ⟩
        upper-n nx z hz = PT.rec (snd ((z ∈ˢ n) ⊔ (z ≈ˢ n))) from-adjoin
          (hb .snd .snd z hz)
          where
          from-adjoin : ⟨ z ∈ˢ u ⟩ ⊎ ⟨ z ≈ˢ x ⟩
            → ⟨ (z ∈ˢ n) ⊔ (z ≈ˢ n) ⟩
          from-adjoin (inl⊎ zu) = upper z zu
          from-adjoin (inr⊎ zx) = case nx
            where
            case : ⟨ n ≈ˢ x ⟩ ⊎ ⟨ x ∈ˢ n ⟩
              → ⟨ (z ∈ˢ n) ⊔ (z ≈ˢ n) ⟩
            case (inl⊎ neqx) = ∣ inr⊎
              (subst (λ q → ⟨ z ≈ˢ q ⟩) (sym (≈→≡ neqx)) zx) ∣₁
            case (inr⊎ x<n) = ∣ inl⊎
              (subst (λ q → ⟨ q ∈ˢ n ⟩) (sym (≈→≡ zx)) x<n) ∣₁

        keep-n : ⟨ n ≈ˢ x ⟩ ⊎ ⟨ x ∈ˢ n ⟩ → ⟨ Bound w b ⟩
        keep-n nx = ∣ n , hn , upper-n nx ∣₁

finite-omits : LEM ℓ → (w : S) → ⟨ CB.isOmega w ⟩
  → (a : S) → ⟨ finiteIn w a ⟩
  → ∥ Σ[ n ∈ S ] (⟨ n ∈ˢ w ⟩ × (⟨ n ∈ˢ a ⟩ → Empty.⊥)) ∥₁
finite-omits lem w hw a ha = PT.rec PT.squash₁ finish (finite-bound lem w hw a ha)
  where
  finish : Σ[ n ∈ S ] (⟨ n ∈ˢ w ⟩ ×
    ((x : S) → ⟨ x ∈ˢ a ⟩ → ⟨ (x ∈ˢ n) ⊔ (x ≈ˢ n) ⟩))
    → ∥ Σ[ s ∈ S ] (⟨ s ∈ˢ w ⟩ × (⟨ s ∈ˢ a ⟩ → Empty.⊥)) ∥₁
  finish (n , hn , upper) = PT.map
    (λ { (s , hs , succ) → s , hs , omitted s succ })
    (hw .fst .snd n hn)
    where
    omitted : (s : S) → ⟨ CB.isSuccOf s n ⟩ → ⟨ s ∈ˢ a ⟩ → Empty.⊥
    omitted s succ hsa = PT.rec Empty.isProp⊥ contradiction (upper s hsa)
      where
      contradiction : ⟨ s ∈ˢ n ⟩ ⊎ ⟨ s ≈ˢ n ⟩ → Empty.⊥
      contradiction (inl⊎ s<n) = CO.no-self find n
        ((omega-members-ordinal w hw n hn) .fst s s<n n (succ .fst))
      contradiction (inr⊎ s=n) = CO.no-self find n
        (subst (λ z → ⟨ n ∈ˢ z ⟩) (≈→≡ s=n) (succ .fst))

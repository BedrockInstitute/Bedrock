{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile

module K7.OrderTypeUniqueness
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
    → ZFStructure._≈ˢ_ 𝒮 x y ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  (find : OrdinaryProfile.FoundationInduction 𝒮)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; Term; var; con; _∈̇_; _≐_; _∧̇_; _⇒̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At; _^_ )
import CardinalBridge
import CodedVocabulary
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_; ⟦_⟧ )

module CB = CardinalBridge 𝒮
module CV = CodedVocabulary 𝒮

≈→≡ : (x y : S) → ⟨ x ≈ˢ y ⟩ → x ≡ y
≈→≡ x y = subst ⟨_⟩ (paths x y)

pattern i0 = zero
pattern i1 = suc i0
pattern i2 = suc i1
pattern i3 = suc i2
pattern i4 = suc i3
pattern i5 = suc i4
pattern i6 = suc i5
pattern i7 = suc i6

triple : ∀ {n} → Term S n → Term S n → Term S n → Fin 3 → Term S n
triple t u v i0 = t
triple t u v i1 = u
triple t u v i2 = v

atThree : ∀ {n} → Formula S 3 → Term S n → Term S n → Term S n → Formula S n
atThree φ t u v = CV.instFo (triple t u v) φ

atThree-reading : ∀ {n} (φ : Formula S 3) (t u v : Term S n) (γ : S ^ n)
  → (γ ⊨ atThree φ t u v) ≡ ((⟦ t ⟧ γ ∷ ⟦ u ⟧ γ ∷ ⟦ v ⟧ γ ∷ []) ⊨ φ)
atThree-reading φ t u v γ = CV.⊨-inst (triple t u v) φ γ
  (⟦ t ⟧ γ ∷ ⟦ u ⟧ γ ∷ ⟦ v ⟧ γ ∷ []) (λ { i0 → refl; i1 → refl; i2 → refl })

Ref : S → S → S → Ω
Ref f x y = ⋁ S (λ p → (p ∈ˢ f) ⊓ CB.isKPair p x y)

refFormula : Formula S 3
refFormula = ∃̇∈ (var i0) (atThree CB.PairφK (var i0) (var i2) (var i3))

ref-reading : (f x y : S) → ((f ∷ x ∷ y ∷ []) ⊨ refFormula) ≡ Ref f x y
ref-reading f x y = cong (⋁ S) (funExt (λ p → cong ((p ∈ˢ f) ⊓_)
  (atThree-reading CB.PairφK (var i0) (var i2) (var i3) (p ∷ f ∷ x ∷ y ∷ [])
    ∙ CB.PairφK-bridge p x y)))

refAt : ∀ {n} → Term S n → Term S n → Term S n → Formula S n
refAt = atThree refFormula

refAt-reading : ∀ {n} (f x y : Term S n) (γ : S ^ n)
  → (γ ⊨ refAt f x y) ≡ Ref (⟦ f ⟧ γ) (⟦ x ⟧ γ) (⟦ y ⟧ γ)
refAt-reading f x y γ = atThree-reading refFormula f x y γ
  ∙ ref-reading (⟦ f ⟧ γ) (⟦ x ⟧ γ) (⟦ y ⟧ γ)

ExactDomain : S → S → Ω
ExactDomain f a = ⋀ S (λ x → ⋀ S (λ u → Ref f x u ⇒ (x ∈ˢ a)))

Onto : S → S → S → Ω
Onto f a A = ⋀ S (λ u → (u ∈ˢ A) ⇒ ⋁ S (λ x → (x ∈ˢ a) ⊓ Ref f x u))

Preserves : S → S → S → Ω
Preserves f a r = ⋀ S (λ x → (x ∈ˢ a) ⇒ ⋀ S (λ y → (y ∈ˢ a) ⇒
  ⋀ S (λ u → ⋀ S (λ v → (Ref f x u ⊓ Ref f y v) ⇒
    (((x ∈ˢ y) ⇒ Ref r u v) ⊓ (Ref r u v ⇒ (x ∈ˢ y)))))))

isOrderIso : S → S → S → S → Ω
isOrderIso f a A r = CB.isInjection f a A ⊓ (ExactDomain f a ⊓ (Onto f a A ⊓ Preserves f a r))

exact-domain-from-onto : (f a A : S) → ⟨ CB.isInjection f a A ⟩
  → ⟨ Onto f a A ⟩ → ⟨ ExactDomain f a ⟩
exact-domain-from-onto f a A hf onto x u fx = PT.rec (snd (x ∈ˢ a))
  (λ { (y , hy , fy) → subst (λ t → ⟨ t ∈ˢ a ⟩)
    (sym (≈→≡ x y (same y fy))) hy }) (onto u range)
  where
  range : ⟨ u ∈ˢ A ⟩
  range = PT.rec (snd (u ∈ˢ A))
    (λ { (p , hp , kp) → hf .snd .snd .fst p hp x u kp }) fx
  same : (y : S) → ⟨ Ref f y u ⟩ → ⟨ x ≈ˢ y ⟩
  same y fy = PT.rec (snd (x ≈ˢ y))
    (λ { (p , hp , kp) → PT.rec (snd (x ≈ˢ y))
      (λ { (q , hq , kq) → hf .snd .snd .snd p hp q hq x u y (kp , kq) }) fy }) fx

order-isomorphism : (f a A r : S) → ⟨ CB.isInjection f a A ⟩
  → ⟨ Onto f a A ⟩ → ⟨ Preserves f a r ⟩ → ⟨ isOrderIso f a A r ⟩
order-isomorphism f a A r hf onto preserves =
  hf , exact-domain-from-onto f a A hf onto , onto , preserves

orderIsoFormula : Formula S 4
orderIsoFormula = atThree CB.IsInjectionφ (var i0) (var i1) (var i2) ∧̇
  ((∀̇ (∀̇ (refAt (var i2) (var i1) (var i0) ⇒̇ (var i1 ∈̇ var i3)))) ∧̇
  ((∀̇∈ (var i2) (∃̇∈ (var i2) (refAt (var i2) (var i0) (var i1)))) ∧̇
  (∀̇∈ (var i1) (∀̇∈ (var i2) (∀̇ (∀̇
    ((refAt (var i4) (var i3) (var i1) ∧̇ refAt (var i4) (var i2) (var i0)) ⇒̇
      (((var i3 ∈̇ var i2) ⇒̇ refAt (var i7) (var i1) (var i0)) ∧̇
       (refAt (var i7) (var i1) (var i0) ⇒̇ (var i3 ∈̇ var i2))))))))))

orderIso-reading : (f a A r : S)
  → ((f ∷ a ∷ A ∷ r ∷ []) ⊨ orderIsoFormula) ≡ isOrderIso f a A r
orderIso-reading f a A r = cong₂ _⊓_
  (atThree-reading CB.IsInjectionφ (var i0) (var i1) (var i2) γ ∙ CB.IsInjection-bridge f a A)
  (cong₂ _⊓_ domain (cong₂ _⊓_ onto preserves))
  where
  γ : S ^ 4
  γ = f ∷ a ∷ A ∷ r ∷ []
  domain = cong (⋀ S) (funExt (λ x → cong (⋀ S) (funExt (λ u →
    cong (_⇒ (x ∈ˢ a)) (refAt-reading (var i2) (var i1) (var i0) (u ∷ x ∷ γ))))))
  onto = cong (⋀ S) (funExt (λ u → cong ((u ∈ˢ A) ⇒_) (cong (⋁ S)
    (funExt (λ x → cong ((x ∈ˢ a) ⊓_) (refAt-reading (var i2) (var i0) (var i1) (x ∷ u ∷ γ)))))))
  preserves = cong (⋀ S) (funExt (λ x → cong ((x ∈ˢ a) ⇒_) (cong (⋀ S)
    (funExt (λ y → cong ((y ∈ˢ a) ⇒_) (cong (⋀ S) (funExt (λ u → cong (⋀ S)
      (funExt (λ v → cong₂ _⇒_
        (cong₂ _⊓_ (refAt-reading (var i4) (var i3) (var i1) (v ∷ u ∷ y ∷ x ∷ γ))
          (refAt-reading (var i4) (var i2) (var i0) (v ∷ u ∷ y ∷ x ∷ γ)))
        (cong₂ _⊓_
          (cong ((x ∈ˢ y) ⇒_) (refAt-reading (var i7) (var i1) (var i0) (v ∷ u ∷ y ∷ x ∷ γ)))
          (cong (_⇒ (x ∈ˢ y)) (refAt-reading (var i7) (var i1) (var i0) (v ∷ u ∷ y ∷ x ∷ γ))))))))))))))

ref-single : (f a A r x u v : S) → ⟨ isOrderIso f a A r ⟩
  → ⟨ Ref f x u ⟩ → ⟨ Ref f x v ⟩ → ⟨ u ≈ˢ v ⟩
ref-single f a A r x u v hf = PT.rec (isPropΠ (λ _ → snd (u ≈ˢ v)))
  (λ { (p , hp , kp) → PT.rec (snd (u ≈ˢ v))
    (λ { (q , hq , kq) → hf .fst .fst .snd p hp q hq x u v (kp , kq) }) })

ref-range : (f a A r x u : S) → ⟨ isOrderIso f a A r ⟩ → ⟨ Ref f x u ⟩ → ⟨ u ∈ˢ A ⟩
ref-range f a A r x u hf = PT.rec (snd (u ∈ˢ A))
  (λ { (p , hp , kp) → hf .fst .snd .snd .fst p hp x u kp })

module Compare (f g a b A r : S)
  (oa : ⟨ CB.isOrdinal a ⟩) (ob : ⟨ CB.isOrdinal b ⟩)
  (hf : ⟨ isOrderIso f a A r ⟩) (hg : ⟨ isOrderIso g b A r ⟩)
  where

  Match : S → Ω
  Match x = (x ∈ˢ a) ⇒ ⋀ S (λ y → (y ∈ˢ b) ⇒ ⋀ S (λ u →
    (Ref f x u ⊓ Ref g y u) ⇒ (x ≈ˢ y)))

  matchFormula : Formula S 1
  matchFormula = (var i0 ∈̇ con a) ⇒̇ ∀̇∈ (con b) (∀̇
    ((refAt (con f) (var i2) (var i0) ∧̇ refAt (con g) (var i1) (var i0))
      ⇒̇ (var i2 ≐ var i1)))

  match-reading : (x : S) → ((x ∷ []) ⊨ matchFormula) ≡ Match x
  match-reading x = cong ((x ∈ˢ a) ⇒_) (cong (⋀ S) (funExt (λ y →
    cong ((y ∈ˢ b) ⇒_) (cong (⋀ S) (funExt (λ u → cong (_⇒ (x ≈ˢ y))
      (cong₂ _⊓_ (refAt-reading (con f) (var i2) (var i0) (u ∷ y ∷ x ∷ []))
        (refAt-reading (con g) (var i1) (var i0) (u ∷ y ∷ x ∷ [])))))))))

  match-step : (x : S) → ((z : S) → ⟨ z ∈ˢ x ⟩ → ⟨ Match z ⟩) → ⟨ Match x ⟩
  match-step x ih hx y hy u (fx , gy) = ext x y (λ z → forward z , backward z)
    where
    forward : (z : S) → ⟨ z ∈ˢ x ⟩ → ⟨ z ∈ˢ y ⟩
    forward z hz = PT.rec (snd (z ∈ˢ y))
      (λ { (v , fv) → PT.rec (snd (z ∈ˢ y))
        (λ { (t , ht , gt) → subst (λ k → ⟨ k ∈ˢ y ⟩)
          (sym (≈→≡ z t (ih z hz (oa .fst x hx z hz) t ht v (fv , gt))))
          (hg .snd .snd .snd t ht y hy v u (gt , gy) .snd
            (hf .snd .snd .snd z (oa .fst x hx z hz) x hx v u (fv , fx) .fst hz)) })
        (hg .snd .snd .fst v (ref-range f a A r z v hf fv)) })
      (hf .fst .snd .fst z (oa .fst x hx z hz))

    backward : (z : S) → ⟨ z ∈ˢ y ⟩ → ⟨ z ∈ˢ x ⟩
    backward z hz = PT.rec (snd (z ∈ˢ x))
      (λ { (v , gv) → PT.rec (snd (z ∈ˢ x))
        (λ { (t , ht , ft) → let
          tx = hf .snd .snd .snd t ht x hx v u (ft , fx) .snd
            (hg .snd .snd .snd z (ob .fst y hy z hz) y hy v u (gv , gy) .fst hz)
          in subst (λ k → ⟨ k ∈ˢ x ⟩)
            (≈→≡ t z (ih t tx ht z (ob .fst y hy z hz) v (ft , gv))) tx })
        (hf .snd .snd .fst v (ref-range g b A r z v hg gv)) })
      (hg .fst .snd .fst z (ob .fst y hy z hz))

  matching-inputs : (x : S) → ⟨ Match x ⟩
  matching-inputs x = subst ⟨_⟩ (match-reading x) (find matchFormula step x)
    where
    step : (z : S) → ((t : S) → ⟨ t ∈ˢ z ⟩ → ⟨ (t ∷ []) ⊨ matchFormula ⟩)
      → ⟨ (z ∷ []) ⊨ matchFormula ⟩
    step z ih = subst ⟨_⟩ (sym (match-reading z))
      (match-step z (λ t ht → subst ⟨_⟩ (match-reading t) (ih t ht)))

  ordertype-unique : ⟨ a ≈ˢ b ⟩
  ordertype-unique = ext a b (λ x → forward x , backward x)
    where
    forward : (x : S) → ⟨ x ∈ˢ a ⟩ → ⟨ x ∈ˢ b ⟩
    forward x hx = PT.rec (snd (x ∈ˢ b))
      (λ { (u , fx) → PT.rec (snd (x ∈ˢ b))
        (λ { (y , hy , gy) → subst (λ t → ⟨ t ∈ˢ b ⟩)
          (sym (≈→≡ x y (matching-inputs x hx y hy u (fx , gy)))) hy })
        (hg .snd .snd .fst u (ref-range f a A r x u hf fx)) })
      (hf .fst .snd .fst x hx)
    backward : (y : S) → ⟨ y ∈ˢ b ⟩ → ⟨ y ∈ˢ a ⟩
    backward y hy = PT.rec (snd (y ∈ˢ a))
      (λ { (u , gy) → PT.rec (snd (y ∈ˢ a))
        (λ { (x , hx , fx) → subst (λ t → ⟨ t ∈ˢ a ⟩)
          (≈→≡ x y (matching-inputs x hx y hy u (fx , gy))) hx })
        (hf .snd .snd .fst u (ref-range g b A r y u hg gy)) })
      (hg .fst .snd .fst y hy)

  same-values : (x u : S) → ⟨ Ref f x u ⟩ → ⟨ Ref g x u ⟩
  same-values x u fx = PT.rec (snd (Ref g x u))
    (λ { (y , hy , gy) → subst (λ t → ⟨ Ref g t u ⟩)
      (sym (≈→≡ x y (matching-inputs x (hf .snd .fst x u fx) y hy u (fx , gy)))) gy })
    (hg .snd .snd .fst u (ref-range f a A r x u hf fx))

ref-ext : (f g : S) → ⟨ CB.isRelation f ⟩ → ⟨ CB.isRelation g ⟩
  → ((x u : S) → ⟨ Ref f x u ⟩ → ⟨ Ref g x u ⟩)
  → ((x u : S) → ⟨ Ref g x u ⟩ → ⟨ Ref f x u ⟩)
  → ⟨ f ≈ˢ g ⟩
ref-ext f g hf hg fg gf = ext f g (λ p → transfer f g hf fg p , transfer g f hg gf p)
  where
  transfer : (f g : S) → ⟨ CB.isRelation f ⟩
    → ((x u : S) → ⟨ Ref f x u ⟩ → ⟨ Ref g x u ⟩)
    → (p : S) → ⟨ p ∈ˢ f ⟩ → ⟨ p ∈ˢ g ⟩
  transfer f g hf h p hp = PT.rec (snd (p ∈ˢ g))
    (λ { (x , hs) → PT.rec (snd (p ∈ˢ g))
      (λ { (u , kp) → PT.rec (snd (p ∈ˢ g))
        (λ { (q , hq , kq) → subst (λ t → ⟨ t ∈ˢ g ⟩)
          (sym (≈→≡ p q (ext p q (λ z →
            (λ hz → kq z .snd (kp z .fst hz)) , (λ hz → kp z .snd (kq z .fst hz)))))) hq })
        (h x u ∣ p , hp , kp ∣₁) }) hs }) (hf p hp)

order-isomorphism-unique : (f g a b A r : S)
  → ⟨ CB.isOrdinal a ⟩ → ⟨ CB.isOrdinal b ⟩
  → ⟨ isOrderIso f a A r ⟩ → ⟨ isOrderIso g b A r ⟩
  → ⟨ (a ≈ˢ b) ⊓ (f ≈ˢ g) ⟩
order-isomorphism-unique f g a b A r oa ob hf hg = Forward.ordertype-unique ,
  ref-ext f g (hf .fst .fst .fst) (hg .fst .fst .fst) Forward.same-values Backward.same-values
  where
  module Forward = Compare f g a b A r oa ob hf hg
  module Backward = Compare g f b a A r ob oa hg hf

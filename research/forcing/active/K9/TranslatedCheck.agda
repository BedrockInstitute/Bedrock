{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile
import K4.Algebra
import K4.Implication
import K5.Frame
import K9.BooleanSeparation
import Cubical.HITs.PropositionalTruncation as PT

module K9.TranslatedCheck
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
    → ZFStructure._≈ˢ_ 𝒮 x y ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  (carrier order B : ZFStructure.S 𝒮)
  (L : K4.Algebra.Lattice 𝒮 B)
  (Cm : K4.Algebra.Complement 𝒮 B L)
  (Kc : K4.Algebra.CodedComplete 𝒮 B L)
  (fb : K5.Frame.Poset.ForcingBase 𝒮 carrier order B L Cm)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open PT using ( ∥_∥₁; ∣_∣₁ )
open K4.Algebra 𝒮 using ( Pt; _≤ᴮ_; ≤ᴮ-refl; ⊆ˢ-trans; isSetPt )
open K4.Algebra.Lattice L
open K4.Implication 𝒮 ext paths B L Cm using ( _⇒ᴮ_; ⇒ᴮ-curry; ≤ᴮ-antisym )
module FP = K5.Frame.Poset 𝒮 carrier order
module FF = FP.Forcing ext paths B L Cm Kc fb
module BS = K9.BooleanSeparation 𝒮 ext paths carrier order B L Cm Kc fb
open FP using ( Cond )
open K5.Frame.Poset.ForcingBase fb using ( i )

≈→≡ : {x y : S} → ⟨ x ≈ˢ y ⟩ → x ≡ y
≈→≡ {x} {y} = subst ⟨_⟩ (paths x y)

≈-refl : (x : S) → ⟨ x ≈ˢ x ⟩
≈-refl x = subst ⟨_⟩ (sym (paths x x)) refl

module Names
  (ind : (P : S → Type ℓ)
    → ((a : S) → ((y : S) → ⟨ y ∈ˢ a ⟩ → P y) → P a) → (a : S) → P a)
  (entry : S → S → S)
  (entry-inj : {x b y c : S} → entry x b ≡ entry y c → (x ≡ y) × (b ≡ c))
  (checkP checkB tr : S → S)
  (checkP-spec : (a e : S) → (e ∈ˢ checkP a)
    ≡ ⋁ S (λ y → (y ∈ˢ a) ⊓ ⋁ S (λ p → (p ∈ˢ carrier)
      ⊓ (e ≈ˢ entry (checkP y) p))))
  (checkB-spec : (a e : S) → (e ∈ˢ checkB a)
    ≡ ⋁ S (λ y → (y ∈ˢ a) ⊓ (e ≈ˢ entry (checkB y) (fst ⊤ᴮ))))
  (tr-entries : (n e : S) → (e ∈ˢ tr n)
    ≡ ⋁ S (λ x → ⋁ S (λ p → ⋁ ⟨ p ∈ˢ carrier ⟩ (λ hp →
      (entry x p ∈ˢ n) ⊓ (e ≈ˢ entry (tr x) (fst (i (p , hp))))))))
  (support : S → S)
  (support-in : (n x b : S) → ⟨ b ∈ˢ B ⟩ → ⟨ entry x b ∈ˢ n ⟩
    → ⟨ x ∈ˢ support n ⟩)
  (support-out : (n x : S) → ⟨ x ∈ˢ support n ⟩
    → ∥ Σ[ b ∈ S ] (⟨ b ∈ˢ B ⟩ × ⟨ entry x b ∈ˢ n ⟩) ∥₁)
  (weight : S → S → Pt B)
  (weight-ub : (n x : S) (b : Pt B) → ⟨ entry x (fst b) ∈ˢ n ⟩
    → ⟨ b ≤ᴮ weight n x ⟩)
  where

  translated : S → S
  translated a = tr (checkP a)

  checked-entry : (a y : S) → ⟨ y ∈ˢ a ⟩
    → ⟨ entry (checkB y) (fst ⊤ᴮ) ∈ˢ checkB a ⟩
  checked-entry a y hy = subst ⟨_⟩ (sym (checkB-spec a _))
    ∣ y , hy , ≈-refl _ ∣₁

  translated-entry : (a y : S) → ⟨ y ∈ˢ a ⟩ → (p : Cond)
    → ⟨ entry (translated y) (fst (i p)) ∈ˢ translated a ⟩
  translated-entry a y hy p = subst ⟨_⟩ (sym (tr-entries (checkP a) _))
    ∣ checkP y , ∣ fst p , ∣ snd p , source , ≈-refl _ ∣₁ ∣₁ ∣₁
    where
    source : ⟨ entry (checkP y) (fst p) ∈ˢ checkP a ⟩
    source = subst ⟨_⟩ (sym (checkP-spec a _))
      ∣ y , hy , ∣ fst p , snd p , ≈-refl _ ∣₁ ∣₁

  checked-support-out : (a x : S) → ⟨ x ∈ˢ support (checkB a) ⟩
    → ∥ Σ[ y ∈ S ] (⟨ y ∈ˢ a ⟩ × (x ≡ checkB y)) ∥₁
  checked-support-out a x hx = PT.rec PT.squash₁
    (λ { (b , hb , e) → PT.map
      (λ { (y , hy , path) → y , hy , fst (entry-inj (≈→≡ path)) })
      (subst ⟨_⟩ (checkB-spec a _) e) }) (support-out (checkB a) x hx)

  translated-support-out : (a x : S) → ⟨ x ∈ˢ support (translated a) ⟩
    → ∥ Σ[ y ∈ S ] (⟨ y ∈ˢ a ⟩ × (x ≡ translated y)) ∥₁
  translated-support-out a x hx = PT.rec PT.squash₁
    (λ { (b , hb , e) → PT.rec PT.squash₁
      (λ { (z , inner) → PT.rec PT.squash₁
        (λ { (p , inner') → PT.rec PT.squash₁
          (λ { (hp , source , path) → PT.rec PT.squash₁
            (λ { (y , hy , ppart) → PT.map
              (λ { (q , hq , sourcepath) → y , hy ,
                fst (entry-inj (≈→≡ path)) ∙
                cong tr (fst (entry-inj (≈→≡ sourcepath))) }) ppart })
            (subst ⟨_⟩ (checkP-spec a _) source) }) inner' }) inner })
      (subst ⟨_⟩ (tr-entries (checkP a) _) e) })
    (support-out (translated a) x hx)

  checked-weight : (a y : S) → ⟨ y ∈ˢ a ⟩ → weight (checkB a) (checkB y) ≡ ⊤ᴮ
  checked-weight a y hy = ≤ᴮ-antisym (⊤-greatest (weight (checkB a) (checkB y)))
    (weight-ub (checkB a) (checkB y) ⊤ᴮ (checked-entry a y hy))

  translated-weight : LEM ℓ → (a y : S) → ⟨ y ∈ˢ a ⟩
    → weight (translated a) (translated y) ≡ ⊤ᴮ
  translated-weight lem a y hy = BS.all-force-top lem (weight (translated a) (translated y))
    (λ p → FF.⊩ᴮ-intro p _
      (weight-ub (translated a) (translated y) (i p) (translated-entry a y hy p)))

  module Values
    (eq mem : S → S → Pt B)
    (mem-ub : (m n x : S) → ⟨ x ∈ˢ support n ⟩
      → ⟨ ((weight n x) ⊓ᴮ (eq m x)) ≤ᴮ mem m n ⟩)
    (eq-glb : (m n : S) (c : Pt B)
      → ((x : S) → ⟨ x ∈ˢ support m ⟩ → ⟨ c ≤ᴮ ((weight m x) ⇒ᴮ (mem x n)) ⟩)
      → ((y : S) → ⟨ y ∈ˢ support n ⟩ → ⟨ c ≤ᴮ ((weight n y) ⇒ᴮ (mem y m)) ⟩)
      → ⟨ c ≤ᴮ eq m n ⟩)
    (eq-sym : (m n : S) → eq m n ≡ eq n m)
    (eq-trans : (m n p : S) → ⟨ ((eq m n) ⊓ᴮ (eq n p)) ≤ᴮ eq m p ⟩)
    where

    top≤ : (b : Pt B) → b ≡ ⊤ᴮ → ⟨ ⊤ᴮ ≤ᴮ b ⟩
    top≤ b h = subst (λ t → ⟨ ⊤ᴮ ≤ᴮ t ⟩) (sym h) (≤ᴮ-refl ⊤ᴮ)

    member-top : (m n x : S) → ⟨ x ∈ˢ support n ⟩
      → weight n x ≡ ⊤ᴮ → eq m x ≡ ⊤ᴮ → ⟨ ⊤ᴮ ≤ᴮ mem m n ⟩
    member-top m n x hx wt eqt = ⊆ˢ-trans
      (⊓-glb (weight n x) (eq m x) ⊤ᴮ (top≤ _ wt) (top≤ _ eqt)) (mem-ub m n x hx)

    comparison : LEM ℓ → (a : S) → eq (translated a) (checkB a) ≡ ⊤ᴮ
    comparison lem = ind (λ a → eq (translated a) (checkB a) ≡ ⊤ᴮ) step
      where
      step : (a : S) → ((y : S) → ⟨ y ∈ˢ a ⟩ → eq (translated y) (checkB y) ≡ ⊤ᴮ)
        → eq (translated a) (checkB a) ≡ ⊤ᴮ
      step a ih = ≤ᴮ-antisym (⊤-greatest (eq (translated a) (checkB a)))
        (eq-glb (translated a) (checkB a) ⊤ᴮ left right)
        where
        left : (x : S) → ⟨ x ∈ˢ support (translated a) ⟩
          → ⟨ ⊤ᴮ ≤ᴮ ((weight (translated a) x) ⇒ᴮ (mem x (checkB a))) ⟩
        left x hx = PT.rec (snd (⊤ᴮ ≤ᴮ ((weight (translated a) x) ⇒ᴮ mem x (checkB a))))
          (λ { (y , hy , path) → ⇒ᴮ-curry ⊤ᴮ (weight (translated a) x) (mem x (checkB a))
            (⊆ˢ-trans (⊤-greatest (⊤ᴮ ⊓ᴮ weight (translated a) x))
              (member-top x (checkB a) (checkB y)
                (support-in (checkB a) (checkB y) (fst ⊤ᴮ) (snd ⊤ᴮ) (checked-entry a y hy))
                (checked-weight a y hy) (cong (λ z → eq z (checkB y)) path ∙ ih y hy))) })
          (translated-support-out a x hx)

        right : (x : S) → ⟨ x ∈ˢ support (checkB a) ⟩
          → ⟨ ⊤ᴮ ≤ᴮ ((weight (checkB a) x) ⇒ᴮ (mem x (translated a))) ⟩
        right x hx = PT.rec (snd (⊤ᴮ ≤ᴮ ((weight (checkB a) x) ⇒ᴮ mem x (translated a))))
          (λ { (y , hy , path) → ⇒ᴮ-curry ⊤ᴮ (weight (checkB a) x) (mem x (translated a))
            (⊆ˢ-trans (⊤-greatest (⊤ᴮ ⊓ᴮ weight (checkB a) x)) (present y hy path)) }) (checked-support-out a x hx)
          where
          present : (y : S) → ⟨ y ∈ˢ a ⟩ → x ≡ checkB y → ⟨ ⊤ᴮ ≤ᴮ mem x (translated a) ⟩
          present y hy path = PT.rec (snd (⊤ᴮ ≤ᴮ mem x (translated a)))
            (λ { (p , hp) → member-top x (translated a) (translated y)
              (support-in (translated a) (translated y) (fst (i (p , hp))) (snd (i (p , hp)))
                (translated-entry a y hy (p , hp)))
              (translated-weight lem a y hy)
              (cong (λ z → eq z (translated y)) path ∙ eq-sym (checkB y) (translated y) ∙ ih y hy) })
            (K5.Frame.Poset.ForcingBase.inhabited fb)

    equality-values : LEM ℓ → (a b : S)
      → eq (translated a) (translated b) ≡ eq (checkB a) (checkB b)
    equality-values lem a b = ≤ᴮ-antisym (bound _ _ _ _ ca cb) (bound _ _ _ _ ac bc)
      where
      ac : eq (translated a) (checkB a) ≡ ⊤ᴮ
      ac = comparison lem a
      bc : eq (translated b) (checkB b) ≡ ⊤ᴮ
      bc = comparison lem b
      ca : eq (checkB a) (translated a) ≡ ⊤ᴮ
      ca = eq-sym (checkB a) (translated a) ∙ ac
      cb : eq (checkB b) (translated b) ≡ ⊤ᴮ
      cb = eq-sym (checkB b) (translated b) ∙ bc

      bound : (x y u v : S) → eq u x ≡ ⊤ᴮ → eq v y ≡ ⊤ᴮ → ⟨ eq x y ≤ᴮ eq u v ⟩
      bound x y u v ux vy = ⊆ˢ-trans
        (⊓-glb (eq u y) (eq y v) (eq x y)
          (⊆ˢ-trans (⊓-glb (eq u x) (eq x y) (eq x y)
            (⊆ˢ-trans (⊤-greatest (eq x y)) (top≤ (eq u x) ux)) (≤ᴮ-refl (eq x y))) (eq-trans u x y))
          (⊆ˢ-trans (⊤-greatest (eq x y)) (top≤ (eq y v) (eq-sym y v ∙ vy))))
        (eq-trans u y v)

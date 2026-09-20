{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile
import CardinalBridge

module K7.OrdinalDiagonal
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
    → ZFStructure._≈ˢ_ 𝒮 x y ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  (pair : OrdinaryProfile.Pairing 𝒮)
  (un : OrdinaryProfile.Union 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (sep : OrdinaryProfile.Separation 𝒮)
  (coll : OrdinaryProfile.Collection 𝒮)
  (find : OrdinaryProfile.FoundationInduction 𝒮)
  (seed : ZFStructure.S 𝒮)
  (lem : LEM ℓ)
  (w : ZFStructure.S 𝒮)
  (hw : ⟨ CardinalBridge.isOmega 𝒮 w ⟩)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _∈̇_; _∧̇_; _⇒̇_; ∃̇∈ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
open import CodedVocabulary 𝒮 using ( isKPairΔ; prAtˢ; subsetΔ; sepAt; sepAt-reading )
import K7.CountableProducts
import K8.DiagonalOrder
import K8.OmegaSuccessor
open import Cubical.Data.Sum using ( inl; inr )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )

module CB = CardinalBridge 𝒮
module CP = K7.CountableProducts 𝒮 ext paths pair un pow sep coll find seed
module Countable = CP.AtOmega lem w hw
module GS = CP.GS
module CO = CP.CO
module DO = K8.DiagonalOrder 𝒮 ext paths pair un pow sep coll find seed lem
module OM = DO.OM
module OS = K8.OmegaSuccessor 𝒮 ext paths pair un pow sep find seed
open OM using ( maxω; _≤ω_ )
open DO using ( Diag; diag-compare; diag-trans; diag-irrefl; diag-max-bound; ≤ω-trans )

ordinal-members : (d : S) → ⟨ CB.isOrdinal d ⟩
  → (a : S) → ⟨ a ∈ˢ d ⟩ → ⟨ CB.isOrdinal a ⟩
ordinal-members d od = find motive step
  where
  motive : Formula S 1
  motive = (var zero ∈̇ con d) ⇒̇ CB.IsOrdinalφ

  step : (x : S) → ((y : S) → ⟨ y ∈ˢ x ⟩ → ⟨ (y ∷ []) ⊨ motive ⟩)
    → ⟨ (x ∷ []) ⊨ motive ⟩
  step x ih hx = transitive , linear
    where
    transitive : (y : S) → ⟨ y ∈ˢ x ⟩ → (z : S) → ⟨ z ∈ˢ y ⟩ → ⟨ z ∈ˢ x ⟩
    transitive y hy z hz = PT.rec (snd (z ∈ˢ x))
      (λ { (inl zx) → zx
         ; (inr h) → PT.rec (snd (z ∈ˢ x))
           (λ { (inl eq) → impossible (subst (λ t → ⟨ t ∈ˢ y ⟩) (GS.≈→≡ eq) hz)
              ; (inr xz) → impossible (oy .fst z hz x xz) }) h })
      (od .snd z (od .fst y (od .fst x hx y hy) z hz) x hx)
      where
      oy : ⟨ CB.isOrdinal y ⟩
      oy = ih y hy (od .fst x hx y hy)
      impossible : ⟨ x ∈ˢ y ⟩ → ⟨ z ∈ˢ x ⟩
      impossible xy = Empty.rec (CO.no-self find y (oy .fst x xy y hy))

    linear : (a : S) → ⟨ a ∈ˢ x ⟩ → (b : S) → ⟨ b ∈ˢ x ⟩
      → ⟨ (a ∈ˢ b) ⊔ ((a ≈ˢ b) ⊔ (b ∈ˢ a)) ⟩
    linear a ha b hb = od .snd a (od .fst x hx a ha) b (od .fst x hx b hb)

pattern i0 = zero
pattern i1 = suc i0
pattern i2 = suc i1
pattern i3 = suc i2
pattern i4 = suc i3
pattern i5 = suc i4
pattern i6 = suc i5
pattern i7 = suc i6

module AtOrdinal (d : S) (od : ⟨ CB.isOrdinal d ⟩)
  (successor-closed : (a : S) → ⟨ a ∈ˢ d ⟩ → ⟨ OS.successor a ∈ˢ d ⟩)
  (members-countable : (a : S) → ⟨ a ∈ˢ d ⟩ → ⟨ CB.injectable a w ⟩)
  where

  P : S
  P = GS.product d d

  ordinal : (a : S) → ⟨ a ∈ˢ d ⟩ → ⟨ CB.isOrdinal a ⟩
  ordinal = ordinal-members d od

  Body : S → S → S → S → S → S → S → S → Ω
  Body p q a b c e m n = isKPairΔ p a b ⊓ (isKPairΔ q c e ⊓
    (OM.maxRel m a b ⊓ (OM.maxRel n c e ⊓ DO.LX.Lex m n (DO.LX.Lex a c (b ∈ˢ e)))))

  lt : S → S → Ω
  lt p q = ⋁ S (λ a → (a ∈ˢ d) ⊓
    ⋁ S (λ b → (b ∈ˢ d) ⊓
    ⋁ S (λ c → (c ∈ˢ d) ⊓
    ⋁ S (λ e → (e ∈ˢ d) ⊓
    ⋁ S (λ m → (m ∈ˢ d) ⊓
    ⋁ S (λ n → (n ∈ˢ d) ⊓ Body p q a b c e m n))))))

  ltFormula : Formula S 2
  ltFormula = ∃̇∈ (con d) (∃̇∈ (con d) (∃̇∈ (con d)
    (∃̇∈ (con d) (∃̇∈ (con d) (∃̇∈ (con d)
      (prAtˢ i6 i5 i4 ∧̇ (prAtˢ i7 i3 i2 ∧̇
        (OM.maxAt i1 i5 i4 ∧̇ (OM.maxAt i0 i3 i2 ∧̇
          DO.LX.lexAt i1 i0 (DO.LX.lexAt i5 i3 (var i4 ∈̇ var i2)))))))))))

  lt-reading : (p q : S) → ((p ∷ q ∷ []) ⊨ ltFormula) ≡ lt p q
  lt-reading p q = refl

  lt-in : (p q a b c e : S)
    → ⟨ a ∈ˢ d ⟩ → ⟨ b ∈ˢ d ⟩ → ⟨ c ∈ˢ d ⟩ → ⟨ e ∈ˢ d ⟩
    → ⟨ isKPairΔ p a b ⟩ → ⟨ isKPairΔ q c e ⟩ → ⟨ Diag a b c e ⟩
    → ⟨ lt p q ⟩
  lt-in p q a b c e ha hb hc he kp kq h =
    ∣ a , ha , ∣ b , hb , ∣ c , hc , ∣ e , he ,
    ∣ maxω a b , OM.maxω-in d a b ha hb ,
    ∣ maxω c e , OM.maxω-in d c e hc he ,
      kp , kq , OM.maxRel-witness a b , OM.maxRel-witness c e , h ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁

  lt-out : (p q a b c e : S) → ⟨ isKPairΔ p a b ⟩ → ⟨ isKPairΔ q c e ⟩
    → ⟨ lt p q ⟩ → ⟨ Diag a b c e ⟩
  lt-out p q a b c e kp kq = PT.rec (snd (Diag a b c e))
    (λ { (a' , _ , h) → PT.rec (snd (Diag a b c e))
    (λ { (b' , _ , h) → PT.rec (snd (Diag a b c e))
    (λ { (c' , _ , h) → PT.rec (snd (Diag a b c e))
    (λ { (e' , _ , h) → PT.rec (snd (Diag a b c e))
    (λ { (m , _ , h) → PT.rec (snd (Diag a b c e))
    (λ { (n , _ , kp' , kq' , hm , hn , h) →
      let ep = GS.ordered-components p a' b' a b kp' kp
          eq = GS.ordered-components q c' e' c e kq' kq
          h' = subst (λ y → ⟨ DO.LX.Lex (maxω a' b') y (DO.LX.Lex a' c' (b' ∈ˢ e')) ⟩)
            (OM.maxRel→maxω n c' e' hn)
            (subst (λ x → ⟨ DO.LX.Lex x n (DO.LX.Lex a' c' (b' ∈ˢ e')) ⟩)
              (OM.maxRel→maxω m a' b' hm) h)
      in subst (λ t → ⟨ Diag a b c t ⟩) (eq .snd)
        (subst (λ t → ⟨ Diag a b t e' ⟩) (eq .fst)
        (subst (λ t → ⟨ Diag a t c' e' ⟩) (ep .snd)
        (subst (λ t → ⟨ Diag t b' c' e' ⟩) (ep .fst) h'))) }) h }) h }) h }) h }) h })

  opaque
    initial : S → S
    initial p = GS.separator P (sepAt ltFormula (p ∷ []))

    initial-spec : (p z : S) → (z ∈ˢ initial p) ≡ ((z ∈ˢ P) ⊓ lt z p)
    initial-spec p z = GS.separator-spec P (sepAt ltFormula (p ∷ [])) z
      ∙ cong ((z ∈ˢ P) ⊓_) (sepAt-reading ltFormula (p ∷ []) z ∙ lt-reading z p)

  trichotomy : (p q : S) → ⟨ p ∈ˢ P ⟩ → ⟨ q ∈ˢ P ⟩
    → ⟨ lt p q ⊔ ((p ≈ˢ q) ⊔ lt q p) ⟩
  trichotomy p q hp hq = PT.rec (snd target)
    (λ { (a , b , ha , hb , kp) → PT.rec (snd target)
    (λ { (c , e , hc , he , kq) → PT.map (λ
      { (inl h) → inl (lt-in p q a b c e ha hb hc he kp kq h)
      ; (inr h) → inr (PT.map (λ
          { (inr k) → inr (lt-in q p c e a b hc he ha hb kq kp k)
          ; (inl (ac , be)) → inl (subst ⟨_⟩ (sym (paths p q))
              (GS.ordered-unique p a b kp ∙ cong₂ GS.ordered (GS.≈→≡ ac) (GS.≈→≡ be)
                ∙ sym (GS.ordered-unique q c e kq))) }) h) })
      (diag-compare a b c e (ordinal a ha) (ordinal b hb) (ordinal c hc) (ordinal e he)) })
      (GS.product-out d d q hq) }) (GS.product-out d d p hp)
    where
    target : Ω
    target = lt p q ⊔ ((p ≈ˢ q) ⊔ lt q p)

  irreflexive : (p : S) → ⟨ p ∈ˢ P ⟩ → ⟨ lt p p ⟩ → Empty.⊥
  irreflexive p hp h = PT.rec Empty.isProp⊥
    (λ { (a , b , _ , _ , kp) → diag-irrefl a b (lt-out p p a b a b kp kp h) })
    (GS.product-out d d p hp)

  transitive : (p q r : S) → ⟨ p ∈ˢ P ⟩ → ⟨ q ∈ˢ P ⟩ → ⟨ r ∈ˢ P ⟩
    → ⟨ lt p q ⟩ → ⟨ lt q r ⟩ → ⟨ lt p r ⟩
  transitive p q r hp hq hr pq qr = PT.rec (snd (lt p r))
    (λ { (a , b , ha , hb , kp) → PT.rec (snd (lt p r))
    (λ { (c , e , hc , he , kq) → PT.rec (snd (lt p r))
    (λ { (f , g , hf , hg , kr) → lt-in p r a b f g ha hb hf hg kp kr
      (diag-trans a b c e f g (ordinal f hf) (ordinal g hg)
        (lt-out p q a b c e kp kq pq) (lt-out q r c e f g kq kr qr)) })
      (GS.product-out d d r hr) }) (GS.product-out d d q hq) }) (GS.product-out d d p hp)

  ≤-in-successor : (a m : S) → ⟨ a ≤ω m ⟩ → ⟨ a ∈ˢ OS.successor m ⟩
  ≤-in-successor a m = PT.rec (snd (a ∈ˢ OS.successor m)) λ
    { (inl am) → OS.successor-spec m .snd .fst a am
    ; (inr eq) → subst (λ z → ⟨ z ∈ˢ OS.successor m ⟩)
        (sym (GS.≈→≡ eq)) (OS.successor-spec m .fst) }

  initial-bound : (p c e : S) → ⟨ c ∈ˢ d ⟩ → ⟨ e ∈ˢ d ⟩
    → ⟨ isKPairΔ p c e ⟩
    → ⟨ subsetΔ (initial p) (GS.product (OS.successor (maxω c e)) (OS.successor (maxω c e))) ⟩
  initial-bound p c e hc he kp z hz = PT.rec (snd (z ∈ˢ GS.product s s))
    (λ { (a , b , ha , hb , kz) →
      let bound = diag-max-bound a b c e
            (lt-out z p a b c e kz kp (subst ⟨_⟩ (initial-spec p z) hz .snd))
          om = OM.maxω-ordinal c e (ordinal c hc) (ordinal e he)
          as = ≤-in-successor a (maxω c e)
            (≤ω-trans a (maxω a b) (maxω c e) om (OM.left≤max a b) bound)
          bs = ≤-in-successor b (maxω c e)
            (≤ω-trans b (maxω a b) (maxω c e) om
              (OM.right≤max a b (ordinal a ha) (ordinal b hb)) bound)
      in subst (λ t → ⟨ t ∈ˢ GS.product s s ⟩) (sym (GS.ordered-unique z a b kz))
        (GS.product-in s s a b as bs) })
    (GS.product-out d d z (subst ⟨_⟩ (initial-spec p z) hz .fst))
    where
    s : S
    s = OS.successor (maxω c e)

  initial-countable : (p : S) → ⟨ p ∈ˢ P ⟩ → ⟨ CB.injectable (initial p) w ⟩
  initial-countable p hp = PT.rec (snd (CB.injectable (initial p) w))
    (λ { (c , e , hc , he , kp) → CO.injectable-mono-dom (initial p)
      (GS.product (OS.successor (maxω c e)) (OS.successor (maxω c e))) w
      (initial-bound p c e hc he kp)
      (Countable.countable-product (OS.successor (maxω c e)) (OS.successor (maxω c e))
        (members-countable (OS.successor (maxω c e))
          (successor-closed (maxω c e) (OM.maxω-in d c e hc he)))
        (members-countable (OS.successor (maxω c e))
          (successor-closed (maxω c e) (OM.maxω-in d c e hc he)))) })
    (GS.product-out d d p hp)

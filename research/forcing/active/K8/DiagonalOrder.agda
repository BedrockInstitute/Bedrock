{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile

module K8.DiagonalOrder
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
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _∈̇_; _∧̇_; ∃̇∈ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
open import CodedVocabulary 𝒮 using ( isKPairΔ; prAtˢ; subsetΔ; sepAt; sepAt-reading )
open import K8.FiniteVocabulary 𝒮 using ( finiteIn )
open import K8.FiniteSubsets 𝒮 ext paths pow sep using ( finite-subset )
import CardinalBridge
import K8.GroundSets
import K8.OmegaMax
import K8.LexOrder
import K8.OmegaFinite
import K8.OmegaInduction
import K8.FiniteProduct
import K8.OmegaPairing
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )
module CB = CardinalBridge 𝒮
module GS = K8.GroundSets.Ground 𝒮 ext paths pair un pow sep seed
module OM = K8.OmegaMax 𝒮 ext paths sep find lem
module LX = K8.LexOrder 𝒮 ext paths sep find lem
module OF = K8.OmegaFinite 𝒮 ext paths pair un pow sep find seed
module OI = K8.OmegaInduction 𝒮 ext paths pair un pow sep seed
module FP = K8.FiniteProduct 𝒮 ext paths pair un pow sep seed
module OP = K8.OmegaPairing 𝒮 ext paths pair un pow sep coll find seed
open GS using ( ≈→≡ )
open OM using ( maxω; _≤ω_; module CO )
open LX using ( Lex; lexAt; lex-irrefl; lex-trans; lex-compare )

pattern i0 = zero
pattern i1 = suc i0
pattern i2 = suc i1
pattern i3 = suc i2
pattern i4 = suc i3
pattern i5 = suc i4
pattern i6 = suc i5
pattern i7 = suc i6

Diag : S → S → S → S → Ω
Diag a b c d = Lex (maxω a b) (maxω c d) (Lex a c (b ∈ˢ d))

diag-irrefl : (a b : S) → ⟨ Diag a b a b ⟩ → Empty.⊥
diag-irrefl a b = lex-irrefl (maxω a b) (Lex a a (b ∈ˢ b))
  (lex-irrefl a (b ∈ˢ b) (CO.no-self find b))

diag-trans : (a b c d e f : S) → ⟨ CB.isOrdinal e ⟩ → ⟨ CB.isOrdinal f ⟩
  → ⟨ Diag a b c d ⟩ → ⟨ Diag c d e f ⟩ → ⟨ Diag a b e f ⟩
diag-trans a b c d e f oe of =
  lex-trans (maxω a b) (maxω c d) (maxω e f)
    (Lex a c (b ∈ˢ d)) (Lex c e (d ∈ˢ f)) (Lex a e (b ∈ˢ f))
    (OM.maxω-ordinal e f oe of)
    (lex-trans a c e (b ∈ˢ d) (d ∈ˢ f) (b ∈ˢ f) oe
      (λ bd df → of .fst d df b bd))

diag-compare : (a b c d : S)
  → ⟨ CB.isOrdinal a ⟩ → ⟨ CB.isOrdinal b ⟩
  → ⟨ CB.isOrdinal c ⟩ → ⟨ CB.isOrdinal d ⟩
  → ⟨ Diag a b c d ⊔ (((a ≈ˢ c) ⊓ (b ≈ˢ d)) ⊔ Diag c d a b) ⟩
diag-compare a b c d oa ob oc od = PT.map (λ
  { (inl h) → inl h
  ; (inr rest) → inr (PT.map (λ { (inl (_ , eq)) → inl eq ; (inr h) → inr h }) rest) })
  (lex-compare (maxω a b) (maxω c d)
    (Lex a c (b ∈ˢ d)) ((a ≈ˢ c) ⊓ (b ≈ˢ d)) (Lex c a (d ∈ˢ b))
    (OM.maxω-ordinal a b oa ob) (OM.maxω-ordinal c d oc od)
    (lex-compare a c (b ∈ˢ d) (b ≈ˢ d) (d ∈ˢ b) oa oc
      (CO.ord-compare find sep lem b d ob od)))

diag-max-bound : (a b c d : S) → ⟨ Diag a b c d ⟩
  → ⟨ maxω a b ≤ω maxω c d ⟩
diag-max-bound a b c d = PT.map λ
  { (inl h) → inl h ; (inr (eq , _)) → inr eq }

≤ω-trans : (a b c : S) → ⟨ CB.isOrdinal c ⟩
  → ⟨ a ≤ω b ⟩ → ⟨ b ≤ω c ⟩ → ⟨ a ≤ω c ⟩
≤ω-trans a b c oc = PT.rec (isPropΠ (λ _ → snd (a ≤ω c))) first
  where
  first : ⟨ a ∈ˢ b ⟩ ⊎ ⟨ a ≈ˢ b ⟩ → ⟨ b ≤ω c ⟩ → ⟨ a ≤ω c ⟩
  first (inl ab) = PT.rec (snd (a ≤ω c)) λ
    { (inl bc) → ∣ inl (oc .fst b bc a ab) ∣₁
    ; (inr eq) → ∣ inl (subst (λ t → ⟨ a ∈ˢ t ⟩) (≈→≡ eq) ab) ∣₁ }
  first (inr eq) = subst (λ t → ⟨ t ≤ω c ⟩) (sym (≈→≡ eq))

module AtOmega (w : S) (hw : ⟨ CB.isOmega w ⟩) where

  P : S
  P = GS.product w w

  ordinal : (a : S) → ⟨ a ∈ˢ w ⟩ → ⟨ CB.isOrdinal a ⟩
  ordinal = OF.omega-members-ordinal w hw

  Body : S → S → S → S → S → S → S → S → Ω
  Body p q a b c d m n = isKPairΔ p a b ⊓ (isKPairΔ q c d ⊓
    (OM.maxRel m a b ⊓ (OM.maxRel n c d ⊓ Lex m n (Lex a c (b ∈ˢ d)))))

  lt : S → S → Ω
  lt p q = ⋁ S (λ a → (a ∈ˢ w) ⊓
    ⋁ S (λ b → (b ∈ˢ w) ⊓
    ⋁ S (λ c → (c ∈ˢ w) ⊓
    ⋁ S (λ d → (d ∈ˢ w) ⊓
    ⋁ S (λ m → (m ∈ˢ w) ⊓
    ⋁ S (λ n → (n ∈ˢ w) ⊓ Body p q a b c d m n))))))

  ltFormula : Formula S 2
  ltFormula = ∃̇∈ (con w) (∃̇∈ (con w) (∃̇∈ (con w)
    (∃̇∈ (con w) (∃̇∈ (con w) (∃̇∈ (con w)
      (prAtˢ i6 i5 i4 ∧̇ (prAtˢ i7 i3 i2 ∧̇
        (OM.maxAt i1 i5 i4 ∧̇ (OM.maxAt i0 i3 i2 ∧̇
          lexAt i1 i0 (lexAt i5 i3 (var i4 ∈̇ var i2)))))))))))

  lt-reading : (p q : S) → ((p ∷ q ∷ []) ⊨ ltFormula) ≡ lt p q
  lt-reading p q = refl

  lt-in : (p q a b c d : S)
    → ⟨ a ∈ˢ w ⟩ → ⟨ b ∈ˢ w ⟩ → ⟨ c ∈ˢ w ⟩ → ⟨ d ∈ˢ w ⟩
    → ⟨ isKPairΔ p a b ⟩ → ⟨ isKPairΔ q c d ⟩ → ⟨ Diag a b c d ⟩
    → ⟨ lt p q ⟩
  lt-in p q a b c d ha hb hc hd kp kq h =
    ∣ a , ha , ∣ b , hb , ∣ c , hc , ∣ d , hd ,
    ∣ maxω a b , OM.maxω-in w a b ha hb ,
    ∣ maxω c d , OM.maxω-in w c d hc hd ,
      kp , kq , OM.maxRel-witness a b , OM.maxRel-witness c d , h ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁

  lt-out : (p q a b c d : S) → ⟨ isKPairΔ p a b ⟩ → ⟨ isKPairΔ q c d ⟩
    → ⟨ lt p q ⟩ → ⟨ Diag a b c d ⟩
  lt-out p q a b c d kp kq = PT.rec (snd (Diag a b c d))
    (λ { (a' , _ , r) → PT.rec (snd (Diag a b c d))
    (λ { (b' , _ , r) → PT.rec (snd (Diag a b c d))
    (λ { (c' , _ , r) → PT.rec (snd (Diag a b c d))
    (λ { (d' , _ , r) → PT.rec (snd (Diag a b c d))
    (λ { (m , _ , r) → PT.rec (snd (Diag a b c d))
    (λ { (n , _ , kp' , kq' , hm , hn , h) →
      let ep = GS.ordered-components p a' b' a b kp' kp
          eq = GS.ordered-components q c' d' c d kq' kq
          h' = subst (λ y → ⟨ Lex (maxω a' b') y (Lex a' c' (b' ∈ˢ d')) ⟩)
            (OM.maxRel→maxω n c' d' hn)
            (subst (λ x → ⟨ Lex x n (Lex a' c' (b' ∈ˢ d')) ⟩)
              (OM.maxRel→maxω m a' b' hm) h)
      in subst (λ t → ⟨ Diag a b c t ⟩) (eq .snd)
        (subst (λ t → ⟨ Diag a b t d' ⟩) (eq .fst)
        (subst (λ t → ⟨ Diag a t c' d' ⟩) (ep .snd)
        (subst (λ t → ⟨ Diag t b' c' d' ⟩) (ep .fst) h'))) }) r }) r }) r }) r }) r })

  initial : S → S
  initial p = GS.separator P (sepAt ltFormula (p ∷ []))

  initial-spec : (p z : S) → (z ∈ˢ initial p) ≡ ((z ∈ˢ P) ⊓ lt z p)
  initial-spec p z = GS.separator-spec P (sepAt ltFormula (p ∷ [])) z
    ∙ cong ((z ∈ˢ P) ⊓_) (sepAt-reading ltFormula (p ∷ []) z ∙ lt-reading z p)

  trichotomy : (p q : S) → ⟨ p ∈ˢ P ⟩ → ⟨ q ∈ˢ P ⟩
    → ⟨ lt p q ⊔ ((p ≈ˢ q) ⊔ lt q p) ⟩
  trichotomy p q hp hq = PT.rec (snd goal)
    (λ { (a , b , ha , hb , kp) → PT.rec (snd goal)
    (λ { (c , d , hc , hd , kq) → PT.map (λ
      { (inl h) → inl (lt-in p q a b c d ha hb hc hd kp kq h)
      ; (inr rest) → inr (PT.map (λ
          { (inr h) → inr (lt-in q p c d a b hc hd ha hb kq kp h)
          ; (inl (ac , bd)) → inl (subst ⟨_⟩ (sym (paths p q))
              (GS.ordered-unique p a b kp ∙ cong₂ GS.ordered (≈→≡ ac) (≈→≡ bd)
                ∙ sym (GS.ordered-unique q c d kq))) }) rest) })
      (diag-compare a b c d (ordinal a ha) (ordinal b hb) (ordinal c hc) (ordinal d hd)) })
      (GS.product-out w w q hq) }) (GS.product-out w w p hp)
    where
    goal : Ω
    goal = lt p q ⊔ ((p ≈ˢ q) ⊔ lt q p)

  irreflexive : (p : S) → ⟨ p ∈ˢ P ⟩ → ⟨ lt p p ⟩ → Empty.⊥
  irreflexive p hp h = PT.rec Empty.isProp⊥
    (λ { (a , b , _ , _ , kp) → diag-irrefl a b (lt-out p p a b a b kp kp h) })
    (GS.product-out w w p hp)

  transitive : (p q r : S) → ⟨ p ∈ˢ P ⟩ → ⟨ q ∈ˢ P ⟩ → ⟨ r ∈ˢ P ⟩
    → ⟨ lt p q ⟩ → ⟨ lt q r ⟩ → ⟨ lt p r ⟩
  transitive p q r hp hq hr pq qr = PT.rec (snd (lt p r))
    (λ { (a , b , ha , hb , kp) → PT.rec (snd (lt p r))
    (λ { (c , d , hc , hd , kq) → PT.rec (snd (lt p r))
    (λ { (e , f , he , hf , kr) → lt-in p r a b e f ha hb he hf kp kr
      (diag-trans a b c d e f (ordinal e he) (ordinal f hf)
        (lt-out p q a b c d kp kq pq) (lt-out q r c d e f kq kr qr)) })
      (GS.product-out w w r hr) }) (GS.product-out w w q hq) }) (GS.product-out w w p hp)

  ≤ω-in-succ : (a m s : S) → ⟨ CB.isSuccOf s m ⟩ → ⟨ a ≤ω m ⟩ → ⟨ a ∈ˢ s ⟩
  ≤ω-in-succ a m s hs = PT.rec (snd (a ∈ˢ s)) λ
    { (inl am) → hs .snd .fst a am
    ; (inr eq) → subst (λ z → ⟨ z ∈ˢ s ⟩) (sym (≈→≡ eq)) (hs .fst) }

  initial-bound : (p c d s : S) → ⟨ c ∈ˢ w ⟩ → ⟨ d ∈ˢ w ⟩
    → ⟨ isKPairΔ p c d ⟩ → ⟨ CB.isSuccOf s (maxω c d) ⟩
    → ⟨ subsetΔ (initial p) (GS.product s s) ⟩
  initial-bound p c d s hc hd kp hs z hz = PT.rec (snd (z ∈ˢ GS.product s s))
    (λ { (a , b , ha , hb , kz) →
      let bound = diag-max-bound a b c d (lt-out z p a b c d kz kp (subst ⟨_⟩ (initial-spec p z) hz .snd))
          om = OM.maxω-ordinal c d (ordinal c hc) (ordinal d hd)
          as = ≤ω-in-succ a (maxω c d) s hs
            (≤ω-trans a (maxω a b) (maxω c d) om (OM.left≤max a b) bound)
          bs = ≤ω-in-succ b (maxω c d) s hs
            (≤ω-trans b (maxω a b) (maxω c d) om
              (OM.right≤max a b (ordinal a ha) (ordinal b hb)) bound)
      in subst (λ t → ⟨ t ∈ˢ GS.product s s ⟩) (sym (GS.ordered-unique z a b kz))
        (GS.product-in s s a b as bs) })
    (GS.product-out w w z (subst ⟨_⟩ (initial-spec p z) hz .fst))

  initial-finite : (p : S) → ⟨ p ∈ˢ P ⟩ → ⟨ finiteIn P (initial p) ⟩
  initial-finite p hp = PT.rec (snd (finiteIn P (initial p)))
    (λ { (c , d , hc , hd , kp) → PT.rec (snd (finiteIn P (initial p)))
    (λ { (s , hs , succ) → finite-subset lem P (GS.product s s) (initial p)
      (FP.finite-product lem w w s s (OI.omega-members-finite w hw s hs)
        (OI.omega-members-finite w hw s hs)) (initial-bound p c d s hc hd kp succ) })
    (hw .fst .snd (maxω c d) (OM.maxω-in w c d hc hd)) }) (GS.product-out w w p hp)

  module Pairing = OP.AtOmega.FiniteInitialOrder lem w hw P lt ltFormula lt-reading
    initial initial-spec initial-finite trichotomy transitive irreflexive

  omega-square-injection : ⟨ CB.injectable (GS.product w w) w ⟩
  omega-square-injection = Pairing.order-injection

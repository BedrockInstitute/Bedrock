{-# OPTIONS --cubical --safe --guardedness #-}
module SheafBoundary where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma using (_×_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Relation.Nullary using (¬_; Dec; yes; no; isPropDec)
open import ModalTrees using (NN; mapNN)
open import BooleanPower using (pointwise-decision)
open import BooleanCompletion

module _ {ℓ : Level}
  (C : Type ℓ)
  (setC : isSet C)
  (stable-equality : (x y : C) → NN (x ≡ y) → x ≡ y)
  (t f : C)
  (distinct : ¬ (t ≡ f))
  (dense : (c : C) → NN ((c ≡ t) ⊎ (c ≡ f)))
  (extend : (D : hProp ℓ) → NN (D .fst) → (g : D .fst → C)
    → Σ[ c ∈ C ] ((d : D .fst) → c ≡ g d)) where

  evaluateC : C → StableProp ℓ
  evaluateC c = ((c ≡ t) , setC c t) , stable-equality c t

  choose-point : (P : StableProp ℓ) → Dec (Holds P) → C
  choose-point P (yes _) = t
  choose-point P (no _) = f

  extended-decision : (P : StableProp ℓ)
    → Σ[ c ∈ C ] ((d : Dec (Holds P)) → c ≡ choose-point P d)
  extended-decision P = extend (Dec (Holds P) , isPropDec (P .fst .snd))
    (pointwise-decision (Holds P)) (choose-point P)

  encode : StableProp ℓ → C
  encode P = extended-decision P .fst

  encode-true : (P : StableProp ℓ) → Holds P → encode P ≡ t
  encode-true P p = extended-decision P .snd (yes p)

  encode-false : (P : StableProp ℓ) → ¬ Holds P → encode P ≡ f
  encode-false P np = extended-decision P .snd (no np)

  decode-true : (P : StableProp ℓ) → encode P ≡ t → Holds P
  decode-true P e = P .snd (mapNN recover (pointwise-decision (Holds P)))
    where
    recover : Dec (Holds P) → Holds P
    recover (yes p) = p
    recover (no np) = Empty.rec (distinct (sym e ∙ encode-false P np))

  evaluate-encode : (P : StableProp ℓ) → evaluateC (encode P) ≡ P
  evaluate-encode P = stable-prop-ext (evaluateC (encode P)) P
    (decode-true P) (encode-true P)

  encode-evaluate : (c : C) → encode (evaluateC c) ≡ c
  encode-evaluate c = stable-equality (encode (evaluateC c)) c
    (mapNN recover (dense c))
    where
    recover : (c ≡ t) ⊎ (c ≡ f) → encode (evaluateC c) ≡ c
    recover (inl e) = encode-true (evaluateC c) e ∙ sym e
    recover (inr e) = encode-false (evaluateC c)
      (λ q → distinct (sym q ∙ e)) ∙ sym e

  abstract-completion-iso : Iso C (StableProp ℓ)
  Iso.fun abstract-completion-iso = evaluateC
  Iso.inv abstract-completion-iso = encode
  Iso.rightInv abstract-completion-iso = evaluate-encode
  Iso.leftInv abstract-completion-iso = encode-evaluate

  abstract-small-classifier : SmallStableClassifier {ℓ}
  abstract-small-classifier = C , isoToEquiv abstract-completion-iso

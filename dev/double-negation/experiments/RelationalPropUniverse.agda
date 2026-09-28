{-# OPTIONS --cubical --safe --guardedness #-}
module RelationalPropUniverse where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Unit using (Unit*; tt*; isPropUnit*)
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Relation.Nullary using (Dec; yes; no)
open import ModalTrees using (NN; unitNN; mapNN; bindNN; propNN; stableNN)
open import BooleanPower using (pointwise-decision)
open import BooleanCompletion using (StableProp; Holds)
open import RelationalTruth using (Classifies; classification-prop;
  classification-stable; classification-total; classification-unique; truth-code)
open import StableRelations
open import RelationalOmega using (Boolean; Truth; classification-respect; classified-agree)

open Object
open Map
open Isomorphism

module _ (ℓ : Level) where
  IsInternalProp : Object ℓ ℓ → Type ℓ
  IsInternalProp A = (x y : Carrier A) → Equal A x y

  PropCode : Type (ℓ-suc ℓ)
  PropCode = Σ[ A ∈ Object ℓ ℓ ] IsInternalProp A

  El : PropCode → Object ℓ ℓ
  El = fst

  truth : PropCode → StableProp ℓ
  truth P = (NN (Carrier (El P)) , propNN) , stableNN

  PropUniverse : Object (ℓ-suc ℓ) ℓ
  Carrier PropUniverse = PropCode
  Equal PropUniverse P Q = Equal (Truth ℓ) (truth P) (truth Q)
  equal-prop PropUniverse P Q = equal-prop (Truth ℓ) (truth P) (truth Q)
  equal-stable PropUniverse P Q = equal-stable (Truth ℓ) (truth P) (truth Q)
  equal-refl PropUniverse P = equal-refl (Truth ℓ) (truth P)
  equal-sym PropUniverse P Q = equal-sym (Truth ℓ) (truth P) (truth Q)
  equal-trans PropUniverse P Q R = equal-trans (Truth ℓ) (truth P) (truth Q) (truth R)

  proposition-object : StableProp ℓ → Object ℓ ℓ
  Carrier (proposition-object P) = Holds P
  Equal (proposition-object P) x y = Unit*
  equal-prop (proposition-object P) x y = isPropUnit*
  equal-stable (proposition-object P) x y n = tt*
  equal-refl (proposition-object P) x = tt*
  equal-sym (proposition-object P) x y eq = tt*
  equal-trans (proposition-object P) x y z eq eq' = tt*

  code : StableProp ℓ → PropCode
  code P = proposition-object P , λ x y → tt*

  code-truth : (P : StableProp ℓ) → Equal (Truth ℓ) (truth (code P)) P
  code-truth P = P .snd , unitNN

  transport-prop : (P Q : PropCode) → Equal PropUniverse P Q → Map (El P) (El Q) ℓ
  graph (transport-prop P Q pq) x y = Unit*
  graph-prop (transport-prop P Q pq) x y = isPropUnit*
  graph-stable (transport-prop P Q pq) x y n = tt*
  respect (transport-prop P Q pq) x x' y y' xx' yy' value = tt*
  total (transport-prop P Q pq) x = mapNN (λ y → y , tt*) (pq .fst (unitNN x))
  unique (transport-prop P Q pq) x y y' value value' = Q .snd y y'

  transport-identity : (P : PropCode)
    → MapEq (transport-prop P P (equal-refl PropUniverse P)) (identity (El P))
  transport-identity P x y = (λ _ → P .snd x y) , (λ _ → tt*)

  transport-composition : (P Q R : PropCode)
    (pq : Equal PropUniverse P Q) (qr : Equal PropUniverse Q R)
    → MapEq (compose (transport-prop Q R qr) (transport-prop P Q pq))
      (transport-prop P R (equal-trans PropUniverse P Q R pq qr))
  transport-composition P Q R pq qr x z =
    (λ _ → tt*) , (λ _ → mapNN (λ y → y , tt* , tt*) (pq .fst (unitNN x)))

  transport-isomorphism : (P Q : PropCode) → Equal PropUniverse P Q
    → Isomorphism (El P) (El Q) ℓ ℓ
  forward (transport-isomorphism P Q pq) = transport-prop P Q pq
  backward (transport-isomorphism P Q pq) = transport-prop Q P (equal-sym PropUniverse P Q pq)
  backward-forward (transport-isomorphism P Q pq) x y =
    (λ _ → P .snd x y) , (λ _ → mapNN (λ q → q , tt* , tt*) (pq .fst (unitNN x)))
  forward-backward (transport-isomorphism P Q pq) x y =
    (λ _ → Q .snd x y) , (λ _ → mapNN (λ p → p , tt* , tt*) (pq .snd (unitNN x)))

  isomorphism-to-code-equality : ∀ {r s} (P Q : PropCode)
    → Isomorphism (El P) (El Q) r s → Equal PropUniverse P Q
  isomorphism-to-code-equality P Q iso =
    (λ n → bindNN n (λ x → mapNN fst (total (forward iso) x))) ,
    (λ n → bindNN n (λ y → mapNN fst (total (backward iso) y)))

  proposition-maps-unique : ∀ {a e r s} {Γ : Object a e}
    (P : PropCode) (F : Map Γ (El P) r) (G : Map Γ (El P) s) → MapEq F G
  proposition-maps-unique {Γ = Γ} P F G x y =
    (λ _ → graph-stable G x y (mapNN (λ { (z , gz) →
      respect G x x z y (equal-refl Γ x) (P .snd z y) gz }) (total G x))) ,
    (λ _ → graph-stable F x y (mapNN (λ { (z , fz) →
      respect F x x z y (equal-refl Γ x) (P .snd z y) fz }) (total F x)))

  classify-code : Map PropUniverse Boolean ℓ
  graph classify-code P b = Classifies (truth P) b
  graph-prop classify-code P b = classification-prop (truth P) b
  graph-stable classify-code P b = classification-stable (truth P) b
  respect classify-code P Q b c pq bc = classification-respect ℓ (truth P) (truth Q) b c pq bc
  total classify-code P = classification-total (truth P)
  unique classify-code P b c = classification-unique (truth P) b c

  boolean-code : Bool → PropCode
  boolean-code b = code (truth-code b)

  boolean-code-classifies : (b : Bool) → Classifies (truth (boolean-code b)) b
  boolean-code-classifies true = unitNN tt*
  boolean-code-classifies false n = n Empty.rec*

  decode-code : Map Boolean PropUniverse ℓ
  graph decode-code b P = Classifies (truth P) b
  graph-prop decode-code b P = classification-prop (truth P) b
  graph-stable decode-code b P = classification-stable (truth P) b
  respect decode-code b c P Q bc pq = classification-respect ℓ (truth P) (truth Q) b c pq bc
  total decode-code b = unitNN (boolean-code b , boolean-code-classifies b)
  unique decode-code b P Q = classified-agree ℓ (truth P) (truth Q) b

  InternalLEM : Type (ℓ-suc ℓ)
  InternalLEM = (P : PropCode) → NN (Dec (Holds (truth P)))

  internal-lem : InternalLEM
  internal-lem P = pointwise-decision (Holds (truth P))

  classify-using-LEM : InternalLEM → Map PropUniverse Boolean ℓ
  classify-using-LEM lem = record classify-code { total = classify-total }
    where
    decide : (P : PropCode) → Dec (Holds (truth P)) → Σ[ b ∈ Bool ] Classifies (truth P) b
    decide P (yes p) = true , p
    decide P (no np) = false , np
    classify-total : (P : PropCode) → NN (Σ[ b ∈ Bool ] Classifies (truth P) b)
    classify-total P = mapNN (decide P) (lem P)

  internal-LEM-to-prop-universe-resizing : InternalLEM → Isomorphism PropUniverse Boolean ℓ ℓ
  forward (internal-LEM-to-prop-universe-resizing lem) = classify-using-LEM lem
  backward (internal-LEM-to-prop-universe-resizing lem) = decode-code
  backward-forward (internal-LEM-to-prop-universe-resizing lem) P Q =
    (λ n → equal-stable PropUniverse P Q (mapNN
      (λ { (b , pb , qb) → classified-agree ℓ (truth P) (truth Q) b pb qb }) n)) ,
    (λ pq → mapNN (λ { (b , pb) → b , pb ,
      classification-respect ℓ (truth P) (truth Q) b b pq refl pb }) (total (classify-using-LEM lem) P))
  forward-backward (internal-LEM-to-prop-universe-resizing lem) b c =
    (λ n → equal-stable Boolean b c (mapNN
      (λ { (P , pb , pc) → classification-unique (truth P) b c pb pc }) n)) ,
    (λ bc → unitNN (boolean-code b , boolean-code-classifies b ,
      subst (Classifies (truth (boolean-code b))) bc (boolean-code-classifies b)))

  prop-universe-resizing : Isomorphism PropUniverse Boolean ℓ ℓ
  prop-universe-resizing = internal-LEM-to-prop-universe-resizing internal-lem

  resizing-with-parameters : ∀ {a e r} {Γ : Object a e} (F : Map Γ PropUniverse r)
    → MapEq (compose decode-code (compose classify-code F)) F
  resizing-with-parameters = context-roundtrip prop-universe-resizing

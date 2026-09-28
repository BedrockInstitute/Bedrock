{-# OPTIONS --cubical --safe --guardedness #-}
module RelationalOmega where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma using (_×_)
open import Cubical.Data.Bool using (Bool; true; false; isSetBool; _≟_)
open import Cubical.Data.Empty as Empty using (⊥)
open import ModalTrees using (NN; unitNN; mapNN)
open import BooleanPower using (decided-stable)
open import BooleanCompletion using (StableProp; Holds)
open import RelationalTruth using (Classifies; classification-prop;
  classification-stable; classification-total; classification-unique;
  truth-code; code-classifies)
open import StableRelations

open Object
open Map
open Isomorphism

Boolean : Object ℓ-zero ℓ-zero
Carrier Boolean = Bool
Equal Boolean = _≡_
equal-prop Boolean = isSetBool
equal-stable Boolean x y = decided-stable (x ≟ y)
equal-refl Boolean x = refl
equal-sym Boolean x y = sym
equal-trans Boolean x y z = _∙_

module _ (ℓ : Level) where
  Truth : Object (ℓ-suc ℓ) ℓ
  Carrier Truth = StableProp ℓ
  Equal Truth P Q = (Holds P → Holds Q) × (Holds Q → Holds P)
  equal-prop Truth P Q = isProp×
    (isPropΠ (λ _ → Q .fst .snd)) (isPropΠ (λ _ → P .fst .snd))
  equal-stable Truth P Q n =
    (λ p → Q .snd (mapNN (λ eq → eq .fst p) n)) ,
    (λ q → P .snd (mapNN (λ eq → eq .snd q) n))
  equal-refl Truth P = (λ p → p) , (λ p → p)
  equal-sym Truth P Q eq = eq .snd , eq .fst
  equal-trans Truth P Q R pq qr =
    (λ p → qr .fst (pq .fst p)) , (λ r → pq .snd (qr .snd r))

  classification-respect : (P Q : StableProp ℓ) (b c : Bool)
    → Equal Truth P Q → b ≡ c → Classifies P b → Classifies Q c
  classification-respect P Q true c pq bc p = subst (Classifies Q) bc (pq .fst p)
  classification-respect P Q false c pq bc np =
    subst (Classifies Q) bc (λ q → np (pq .snd q))

  classified-agree : (P Q : StableProp ℓ) (b : Bool)
    → Classifies P b → Classifies Q b → Equal Truth P Q
  classified-agree P Q true p q = (λ _ → q) , (λ _ → p)
  classified-agree P Q false np nq =
    (λ p → Empty.rec (np p)) , (λ q → Empty.rec (nq q))

  encode : Map Truth Boolean ℓ
  graph encode = Classifies
  graph-prop encode = classification-prop
  graph-stable encode = classification-stable
  respect encode = classification-respect
  total encode = classification-total
  unique encode = classification-unique

  decode : Map Boolean Truth ℓ
  graph decode b P = Classifies P b
  graph-prop decode b P = classification-prop P b
  graph-stable decode b P = classification-stable P b
  respect decode b c P Q bc pq = classification-respect P Q b c pq bc
  total decode b = unitNN (truth-code b , code-classifies b)
  unique decode b P Q = classified-agree P Q b

  decode-encode : MapEq (compose decode encode) (identity Truth)
  decode-encode P Q =
    (λ n → equal-stable Truth P Q
      (mapNN (λ { (b , pb , qb) → classified-agree P Q b pb qb }) n)) ,
    (λ pq → mapNN (λ { (b , pb) → b , pb ,
      classification-respect P Q b b pq refl pb }) (classification-total P))

  encode-decode : MapEq (compose encode decode) (identity Boolean)
  encode-decode b c =
    (λ n → equal-stable Boolean b c
      (mapNN (λ { (P , pb , pc) → classification-unique P b c pb pc }) n)) ,
    (λ bc → unitNN (truth-code b , code-classifies b ,
      subst (Classifies (truth-code b)) bc (code-classifies b)))

  truth-boolean-isomorphism : Isomorphism Truth Boolean ℓ ℓ
  forward truth-boolean-isomorphism = encode
  backward truth-boolean-isomorphism = decode
  backward-forward truth-boolean-isomorphism = decode-encode
  forward-backward truth-boolean-isomorphism = encode-decode

  classifier-roundtrip : ∀ {c e r} {Γ : Object c e} (F : Map Γ Truth r)
    → MapEq (compose decode (compose encode F)) F
  classifier-roundtrip = context-roundtrip truth-boolean-isomorphism

  classifier-substitution : ∀ {c e d f r s} {Γ : Object c e} {Δ : Object d f}
    (F : Map Γ Truth r) (σ : Map Δ Γ s)
    → MapEq (compose encode (compose F σ)) (compose (compose encode F) σ)
  classifier-substitution = context-substitution truth-boolean-isomorphism

  RelationalOmegaResizing : Type (ℓ-suc ℓ)
  RelationalOmegaResizing = Σ[ O ∈ Object ℓ-zero ℓ-zero ] Isomorphism Truth O ℓ ℓ

  relational-omega-resizing : RelationalOmegaResizing
  relational-omega-resizing = Boolean , truth-boolean-isomorphism

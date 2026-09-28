{-# OPTIONS --cubical --safe --guardedness #-}
module RelationalClassifier where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma using (_×_)
open import Cubical.Data.Bool using (Bool; true; false; false≢true)
open import Cubical.Data.Empty as Empty using (⊥)
open import ModalTrees using (NN; unitNN; mapNN; bindNN; propNN; stableNN)
open import BooleanCompletion using (StableProp; Holds)
open import RelationalTruth using (Classifies; classification-prop;
  classification-stable; classification-total; classification-unique)
open import StableRelations
open import RelationalOmega using (Boolean; Truth; classification-respect)

open Object
open Map

record Predicate {a e : Level} (A : Object a e) (p : Level)
  : Type (ℓ-max (ℓ-suc (ℓ-max a p)) e) where
  field
    value : Carrier A → StableProp p
    invariant : (x y : Carrier A) → Equal A x y → Holds (value x) → Holds (value y)

open Predicate

PredicateEq : ∀ {a e p q} {A : Object a e} → Predicate A p → Predicate A q
  → Type (ℓ-max a (ℓ-max p q))
PredicateEq P Q = ∀ x → (Holds (value P x) → Holds (value Q x)) ×
  (Holds (value Q x) → Holds (value P x))

classify : ∀ {a e p} {A : Object a e} → Predicate A p → Map A Boolean p
graph (classify P) x b = Classifies (value P x) b
graph-prop (classify P) x b = classification-prop (value P x) b
graph-stable (classify P) x b = classification-stable (value P x) b
respect (classify {p = p} {A = A} P) x y b c xy bc =
  classification-respect p (value P x) (value P y) b c
    (invariant P x y xy , invariant P y x (equal-sym A x y xy)) bc
total (classify P) x = classification-total (value P x)
unique (classify P) x b c = classification-unique (value P x) b c

read : ∀ {a e r} {A : Object a e} → Map A Boolean r → Predicate A r
value (read F) x = (graph F x true , graph-prop F x true) , graph-stable F x true
invariant (read F) x y xy = respect F x y true true xy refl

read-classify : ∀ {a e p} {A : Object a e} (P : Predicate A p)
  → PredicateEq (read (classify P)) P
read-classify P x = (λ p → p) , (λ p → p)

classify-read : ∀ {a e r} {A : Object a e} (F : Map A Boolean r)
  → MapEq (classify (read F)) F
classify-read F x true = (λ p → p) , (λ p → p)
classify-read F x false =
  (λ not-true → graph-stable F x false (mapNN
    (λ { (true , t) → Empty.rec (not-true t) ; (false , f) → f }) (total F x))) ,
  (λ f t → false≢true (unique F x false true f t))

pullback : ∀ {a e b d r p} {A : Object a e} {B : Object b d}
  → Map A B r → Predicate B p → Predicate A (ℓ-max b (ℓ-max r p))
value (pullback σ P) x =
  (NN (Σ[ y ∈ _ ] (graph σ x y × Holds (value P y))) , propNN) , stableNN
invariant (pullback {B = B} σ P) x x' eq = mapNN
  (λ { (y , σxy , py) → y , respect σ x x' y y eq (equal-refl B y) σxy , py })

classifier-pullback : ∀ {a e b d r p} {A : Object a e} {B : Object b d}
  (σ : Map A B r) (P : Predicate B p)
  → MapEq (classify (pullback σ P)) (compose (classify P) σ)
classifier-pullback σ P x true = (λ n → n) , (λ n → n)
classifier-pullback σ P x false =
  (λ negative → mapNN (λ { (y , σxy) → y , σxy ,
    λ py → negative (unitNN (y , σxy , py)) }) (total σ x)) ,
  (λ negative positive → bindNN negative (λ { (y , σxy , npy) →
    mapNN (λ { (z , σxz , pz) → npy
      (invariant P z y (unique σ x z y σxz σxy) pz) }) positive }) (λ z → z))

comprehension : ∀ {a e p} {A : Object a e} → Predicate A p → Object (ℓ-max a p) e
Carrier (comprehension {A = A} P) = Σ[ x ∈ Carrier A ] Holds (value P x)
Equal (comprehension {A = A} P) x y = Equal A (x .fst) (y .fst)
equal-prop (comprehension {A = A} P) x y = equal-prop A (x .fst) (y .fst)
equal-stable (comprehension {A = A} P) x y = equal-stable A (x .fst) (y .fst)
equal-refl (comprehension {A = A} P) x = equal-refl A (x .fst)
equal-sym (comprehension {A = A} P) x y = equal-sym A (x .fst) (y .fst)
equal-trans (comprehension {A = A} P) x y z =
  equal-trans A (x .fst) (y .fst) (z .fst)

inclusion : ∀ {a e p} {A : Object a e} (P : Predicate A p) → Map (comprehension P) A e
graph (inclusion {A = A} P) x y = Equal A (x .fst) y
graph-prop (inclusion {A = A} P) x y = equal-prop A (x .fst) y
graph-stable (inclusion {A = A} P) x y = equal-stable A (x .fst) y
respect (inclusion {A = A} P) x x' y y' xx' yy' xy =
  respect (identity A) (x .fst) (x' .fst) y y' xx' yy' xy
total (inclusion {A = A} P) x = unitNN (x .fst , equal-refl A (x .fst))
unique (inclusion {A = A} P) x y y' = unique (identity A) (x .fst) y y'

universal-truth : (ℓ : Level) → Predicate (Truth ℓ) ℓ
value (universal-truth ℓ) P = P
invariant (universal-truth ℓ) P Q pq = pq .fst

comprehension-small : ∀ {ℓ} {A : Object ℓ ℓ}
  → Predicate A ℓ → Object ℓ ℓ
comprehension-small = comprehension

name-predicate : ∀ {a e p} {A : Object a e} → Predicate A p → Map A (Truth p) p
graph (name-predicate {p = p} P) x Q = Equal (Truth p) (value P x) Q
graph-prop (name-predicate {p = p} P) x Q = equal-prop (Truth p) (value P x) Q
graph-stable (name-predicate {p = p} P) x Q = equal-stable (Truth p) (value P x) Q
respect (name-predicate {p = p} {A = A} P) x y Q R xy qr pq =
  respect (identity (Truth p)) (value P x) (value P y) Q R
    (invariant P x y xy , invariant P y x (equal-sym A x y xy)) qr pq
total (name-predicate {p = p} P) x = unitNN (value P x , equal-refl (Truth p) (value P x))
unique (name-predicate {p = p} P) x Q R = unique (identity (Truth p)) (value P x) Q R

decode-name : ∀ {a e p} {A : Object a e} (P : Predicate A p)
  → PredicateEq (pullback (name-predicate P) (universal-truth p)) P
decode-name P x =
  (λ n → value P x .snd (mapNN (λ { (Q , pq , q) → pq .snd q }) n)) ,
  (λ p → unitNN (value P x , ((λ p → p) , (λ p → p)) , p))

pullback-identity : ∀ {a e p} {A : Object a e} (P : Predicate A p)
  → PredicateEq (pullback (identity A) P) P
pullback-identity {A = A} P x =
  (λ n → value P x .snd (mapNN
    (λ { (y , xy , py) → invariant P y x (equal-sym A x y xy) py }) n)) ,
  (λ px → unitNN (x , equal-refl A x , px))

pullback-composition : ∀ {a e b d c f r s p}
  {A : Object a e} {B : Object b d} {C : Object c f}
  (σ : Map B C s) (τ : Map A B r) (P : Predicate C p)
  → PredicateEq (pullback (compose σ τ) P) (pullback τ (pullback σ P))
pullback-composition σ τ P x =
  (λ n → bindNN n λ { (z , στ , pz) → mapNN
    (λ { (y , τxy , σyz) → y , τxy , unitNN (z , σyz , pz) }) στ }) ,
  (λ n → bindNN n λ { (y , τxy , σp) → mapNN
    (λ { (z , σyz , pz) → z , unitNN (y , τxy , σyz) , pz }) σp })

pullback-congruent : ∀ {a e b d r s p q} {A : Object a e} {B : Object b d}
  {σ : Map A B r} {τ : Map A B s} {P : Predicate B p} {Q : Predicate B q}
  → MapEq σ τ → PredicateEq P Q → PredicateEq (pullback σ P) (pullback τ Q)
pullback-congruent στ pq x =
  mapNN (λ { (y , σxy , py) → y , στ x y .fst σxy , pq y .fst py }) ,
  mapNN (λ { (y , τxy , qy) → y , στ x y .snd τxy , pq y .snd qy })

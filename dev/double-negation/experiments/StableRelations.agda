{-# OPTIONS --cubical --safe --guardedness #-}
module StableRelations where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma using (_×_)
open import ModalTrees using (NN; unitNN; mapNN; bindNN; propNN; stableNN)

record Object (a e : Level) : Type (ℓ-suc (ℓ-max a e)) where
  field
    Carrier : Type a
    Equal : Carrier → Carrier → Type e
    equal-prop : (x y : Carrier) → isProp (Equal x y)
    equal-stable : (x y : Carrier) → NN (Equal x y) → Equal x y
    equal-refl : (x : Carrier) → Equal x x
    equal-sym : (x y : Carrier) → Equal x y → Equal y x
    equal-trans : (x y z : Carrier) → Equal x y → Equal y z → Equal x z

open Object

record Map {a e b d : Level} (A : Object a e) (B : Object b d) (r : Level)
  : Type (ℓ-max (ℓ-max a b) (ℓ-max (ℓ-suc r) (ℓ-max e d))) where
  field
    graph : Carrier A → Carrier B → Type r
    graph-prop : (x : Carrier A) (y : Carrier B) → isProp (graph x y)
    graph-stable : (x : Carrier A) (y : Carrier B) → NN (graph x y) → graph x y
    respect : (x x' : Carrier A) (y y' : Carrier B)
      → Equal A x x' → Equal B y y' → graph x y → graph x' y'
    total : (x : Carrier A) → NN (Σ[ y ∈ Carrier B ] graph x y)
    unique : (x : Carrier A) (y y' : Carrier B)
      → graph x y → graph x y' → Equal B y y'

open Map

MapEq : ∀ {a e b d r s} {A : Object a e} {B : Object b d}
  → Map A B r → Map A B s → Type (ℓ-max (ℓ-max a b) (ℓ-max r s))
MapEq F G = ∀ x y → (graph F x y → graph G x y) × (graph G x y → graph F x y)

map-eq-refl : ∀ {a e b d r} {A : Object a e} {B : Object b d}
  (F : Map A B r) → MapEq F F
map-eq-refl F x y = (λ p → p) , (λ p → p)

map-eq-sym : ∀ {a e b d r s} {A : Object a e} {B : Object b d}
  {F : Map A B r} {G : Map A B s} → MapEq F G → MapEq G F
map-eq-sym eq x y = eq x y .snd , eq x y .fst

map-eq-trans : ∀ {a e b d r s t} {A : Object a e} {B : Object b d}
  {F : Map A B r} {G : Map A B s} {H : Map A B t}
  → MapEq F G → MapEq G H → MapEq F H
map-eq-trans fg gh x y =
  (λ p → gh x y .fst (fg x y .fst p)) , (λ p → fg x y .snd (gh x y .snd p))

identity : ∀ {a e} (A : Object a e) → Map A A e
graph (identity A) = Equal A
graph-prop (identity A) = equal-prop A
graph-stable (identity A) = equal-stable A
respect (identity A) x x' y y' xx' yy' xy = equal-trans A x' y y'
  (equal-trans A x' x y (equal-sym A x x' xx') xy) yy'
total (identity A) x = unitNN (x , equal-refl A x)
unique (identity A) x y y' xy xy' = equal-trans A y x y' (equal-sym A x y xy) xy'

compose : ∀ {a e b d c f r s} {A : Object a e} {B : Object b d} {C : Object c f}
  → Map B C s → Map A B r → Map A C (ℓ-max b (ℓ-max r s))
graph (compose G F) x z = NN (Σ[ y ∈ _ ] (graph F x y × graph G y z))
graph-prop (compose G F) x z = propNN
graph-stable (compose G F) x z = stableNN
respect (compose {B = B} G F) x x' z z' xx' zz' n = mapNN
  (λ { (y , fy , gy) → y ,
    respect F x x' y y xx' (equal-refl B y) fy ,
    respect G y y z z' (equal-refl B y) zz' gy }) n
total (compose G F) x = bindNN (total F x) λ { (y , fy) →
  mapNN (λ { (z , gz) → z , unitNN (y , fy , gz) }) (total G y) }
unique (compose {B = B} {C = C} G F) x z z' left right = equal-stable C z z'
  (bindNN left λ { (y , fy , gy) → mapNN
    (λ { (y' , fy' , gy') → unique G y' z z'
      (respect G y y' z z (unique F x y y' fy fy') (equal-refl C z) gy) gy' }) right })

compose-congruent : ∀ {a e b d c f r r' s s'}
  {A : Object a e} {B : Object b d} {C : Object c f}
  {F : Map A B r} {F' : Map A B r'} {G : Map B C s} {G' : Map B C s'}
  → MapEq G G' → MapEq F F' → MapEq (compose G F) (compose G' F')
compose-congruent gg ff x z =
  mapNN (λ { (y , fy , gy) → y , ff x y .fst fy , gg y z .fst gy }) ,
  mapNN (λ { (y , fy , gy) → y , ff x y .snd fy , gg y z .snd gy })

left-unit : ∀ {a e b d r} {A : Object a e} {B : Object b d}
  (F : Map A B r) → MapEq (compose (identity B) F) F
left-unit {A = A} {B = B} F x z =
  (λ n → graph-stable F x z (mapNN
    (λ { (y , fy , yz) → respect F x x y z (equal-refl A x) yz fy }) n)) ,
  (λ fz → unitNN (z , fz , equal-refl B z))

right-unit : ∀ {a e b d r} {A : Object a e} {B : Object b d}
  (F : Map A B r) → MapEq (compose F (identity A)) F
right-unit {A = A} {B = B} F x z =
  (λ n → graph-stable F x z (mapNN
    (λ { (y , xy , fy) → respect F y x z z (equal-sym A x y xy) (equal-refl B z) fy }) n)) ,
  (λ fz → unitNN (x , equal-refl A x , fz))

associative : ∀ {a e b d c f h k r s t}
  {A : Object a e} {B : Object b d} {C : Object c f} {D : Object h k}
  (H : Map C D t) (G : Map B C s) (F : Map A B r)
  → MapEq (compose H (compose G F)) (compose (compose H G) F)
associative H G F x w =
  (λ n → bindNN n λ { (z , gf , hz) → mapNN
    (λ { (y , fy , gy) → y , fy , unitNN (z , gy , hz) }) gf }) ,
  (λ n → bindNN n λ { (y , fy , hg) → mapNN
    (λ { (z , gy , hz) → z , unitNN (y , fy , gy) , hz }) hg })

record Isomorphism {a e b d : Level} (A : Object a e) (B : Object b d) (r s : Level)
  : Type (ℓ-max (ℓ-max a b) (ℓ-max (ℓ-max e d) (ℓ-suc (ℓ-max r s)))) where
  field
    forward : Map A B r
    backward : Map B A s
    backward-forward : MapEq (compose backward forward) (identity A)
    forward-backward : MapEq (compose forward backward) (identity B)

module _ {a e b d r s} {A : Object a e} {B : Object b d}
  (iso : Isomorphism A B r s) where
  open Isomorphism iso

  context-roundtrip : ∀ {c f t} {Γ : Object c f} (F : Map Γ A t)
    → MapEq (compose backward (compose forward F)) F
  context-roundtrip F x y =
    (λ p → third .fst (second .fst (first .fst p))) ,
    (λ p → first .snd (second .snd (third .snd p)))
    where
    first = associative backward forward F x y
    second = compose-congruent {F = F} {F' = F}
      {G = compose backward forward} {G' = identity A}
      backward-forward (map-eq-refl F) x y
    third = left-unit F x y

  reverse-context-roundtrip : ∀ {c f t} {Γ : Object c f} (F : Map Γ B t)
    → MapEq (compose forward (compose backward F)) F
  reverse-context-roundtrip F x y =
    (λ p → third .fst (second .fst (first .fst p))) ,
    (λ p → first .snd (second .snd (third .snd p)))
    where
    first = associative forward backward F x y
    second = compose-congruent {F = F} {F' = F}
      {G = compose forward backward} {G' = identity B}
      forward-backward (map-eq-refl F) x y
    third = left-unit F x y

  context-substitution : ∀ {c f h k t u} {Γ : Object c f} {Δ : Object h k}
    (F : Map Γ A t) (σ : Map Δ Γ u)
    → MapEq (compose forward (compose F σ)) (compose (compose forward F) σ)
  context-substitution = associative forward

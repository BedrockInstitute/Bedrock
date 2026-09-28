{-# OPTIONS --cubical --safe --guardedness #-}
module DensePower where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma using (_×_)
open import Cubical.Data.Unit using (Unit; tt)
open import ModalTrees
open import BooleanPower using (Subset; cut; cut-subset; canonical-subset;
  boolPower; boolPower-sound; boolPower-complete; pointwise-decision)

module _ {ℓ : Level} {A : Type ℓ} (f : A → Tree ℓ) where
  record Predicate : Type (ℓ-suc ℓ) where
    field
      holds : A → Type ℓ
      prop : (i : A) → isProp (holds i)
      stable : (i : A) → NN (holds i) → holds i
      saturated : (i j : A) → Eq (f i) (f j) → holds i → holds j

  open Predicate

  Agree : Predicate → Predicate → Type ℓ
  Agree P R = (i : A) → (holds P i → holds R i) × (holds R i → holds P i)

  cutPredicate : Predicate → Tree ℓ
  cutPredicate P = cut f (holds P)

  cut-in : (P : Predicate) (i : A) → holds P i → Mem (f i) (cutPredicate P)
  cut-in P i p = unitNN ((i , p) , eq-refl (f i))

  cut-out : (P : Predicate) (i : A) → Mem (f i) (cutPredicate P) → holds P i
  cut-out P i m = stable P i (mapNN
    (λ { ((j , p) , e) → saturated P j i (eq-sym (f i) (f j) e) p }) m)

  agree-cut : (P R : Predicate) → Agree P R → Eq (cutPredicate P) (cutPredicate R)
  agree-cut P R agree =
    (λ { (i , p) → unitNN ((i , agree i .fst p) , eq-refl (f i)) }) ,
    (λ { (i , r) → unitNN ((i , agree i .snd r) , eq-refl (f i)) })

  memberPredicate : Tree ℓ → Predicate
  holds (memberPredicate b) i = Mem (f i) b
  prop (memberPredicate b) i = mem-prop (f i) b
  stable (memberPredicate b) i = mem-stable (f i) b
  saturated (memberPredicate b) i j = mem-left (f i) (f j) b

  record DenseCover : Type (ℓ-suc ℓ) where
    field
      Index : Type ℓ
      family : Index → Predicate
      covers : (P : Predicate) → NN (Σ[ i ∈ Index ] Agree P (family i))

  record PowerWitness : Type (ℓ-suc ℓ) where
    field
      power : Tree ℓ
      sound : (b : Tree ℓ) → Mem b power → Subset b (sup A f)
      complete : (b : Tree ℓ) → Subset b (sup A f) → Mem b power

  open DenseCover
  open PowerWitness

  cover-to-power : DenseCover → PowerWitness
  power (cover-to-power C) = sup (Index C) (λ i → cutPredicate (family C i))
  sound (cover-to-power C) b mb x mx = mem-stable x (sup A f)
    (mapNN (λ { (i , e) → cut-subset f (holds (family C i)) x
      (mem-right x b (cutPredicate (family C i)) e mx) }) mb)
  complete (cover-to-power C) b sub = mapNN
    (λ { (i , agree) → i , eq-trans b (cutPredicate (memberPredicate b))
      (cutPredicate (family C i)) (canonical-subset (sup A f) b sub)
      (agree-cut (memberPredicate b) (family C i) agree) })
    (covers C (memberPredicate b))

  power-to-cover : PowerWitness → DenseCover
  power-to-cover W = build (power W) (complete W)
    where
    build : (p : Tree ℓ)
      → ((b : Tree ℓ) → Subset b (sup A f) → Mem b p) → DenseCover
    Index (build (sup I g) complete-p) = I
    family (build (sup I g) complete-p) i = memberPredicate (g i)
    covers (build (sup I g) complete-p) P = mapNN
      (λ { (i , e) → i , λ j →
        (λ q → mem-right (f j) (cutPredicate P) (g i) e (cut-in P j q)) ,
        (λ m → cut-out P j (mem-right (f j) (g i) (cutPredicate P)
          (eq-sym (cutPredicate P) (g i) e) m)) })
      (complete-p (cutPredicate P) (cut-subset f (holds P)))

  negative-cover-to-power : NN DenseCover → NN PowerWitness
  negative-cover-to-power = mapNN cover-to-power

  negative-power-to-cover : NN PowerWitness → NN DenseCover
  negative-power-to-cover = mapNN power-to-cover

module _ (x : Tree ℓ-zero) where
  singletonPresentation : Unit → Tree ℓ-zero
  singletonPresentation _ = x

  singleton-power : PowerWitness singletonPresentation
  PowerWitness.power singleton-power = boolPower (sup Unit singletonPresentation)
  PowerWitness.sound singleton-power = boolPower-sound (sup Unit singletonPresentation)
  PowerWitness.complete singleton-power b = boolPower-complete singletonPresentation b
    (mapNN (λ d _ → d) (pointwise-decision (Mem x b)))

  singleton-cover : DenseCover singletonPresentation
  singleton-cover = power-to-cover singletonPresentation singleton-power

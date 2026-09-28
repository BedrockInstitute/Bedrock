{-# OPTIONS --cubical --safe --guardedness #-}
module RelationalFunctionBoundary where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; discreteℕ; isSetℕ)
open import Cubical.Data.Bool using (Bool; true)
open import Cubical.Relation.Nullary using (¬_)
open import ModalTrees using (NN; mapNN)
open import BooleanPower using (decided-stable)
open import BooleanCompletion using (Holds)
open import RelationalTruth using (Pred; PredicateCover)
open import SubcountableObstruction using (Subcountable; ModalAllSmallSubcountable;
  cover-index-not-subcountable)
open import StableRelations
open import RelationalOmega using (Boolean)
open import RelationalClassifier using (Predicate; classify; read)

open Object
open Map
open Predicate

Natural : Object ℓ-zero ℓ-zero
Carrier Natural = ℕ
Equal Natural = _≡_
equal-prop Natural = isSetℕ
equal-stable Natural x y = decided-stable (discreteℕ x y)
equal-refl Natural x = refl
equal-sym Natural x y = sym
equal-trans Natural x y z = _∙_

natural-predicate : Pred ℕ → Predicate Natural ℓ-zero
value (natural-predicate P) = P
invariant (natural-predicate P) x y eq = subst (λ n → Holds (P n)) eq

record SmallHomPresentation : Type₁ where
  field
    Index : Type
    family : Index → Map Natural Boolean ℓ-zero
    covers : (F : Map Natural Boolean ℓ-zero)
      → NN (Σ[ i ∈ Index ] MapEq F (family i))

hom-presentation-to-predicate-cover : SmallHomPresentation → PredicateCover ℕ
PredicateCover.Index (hom-presentation-to-predicate-cover H) = SmallHomPresentation.Index H
PredicateCover.family (hom-presentation-to-predicate-cover H) i =
  value (read (SmallHomPresentation.family H i))
PredicateCover.covers (hom-presentation-to-predicate-cover H) P = mapNN
  (λ { (i , agrees) → i , λ n → agrees n true })
  (SmallHomPresentation.covers H (classify (natural-predicate P)))

hom-presentation-not-subcountable : (H : SmallHomPresentation)
  → ¬ Subcountable (SmallHomPresentation.Index H)
hom-presentation-not-subcountable H =
  cover-index-not-subcountable (hom-presentation-to-predicate-cover H)

modal-subcountability-refutes-small-homs : ModalAllSmallSubcountable → ¬ SmallHomPresentation
modal-subcountability-refutes-small-homs sc H =
  sc (SmallHomPresentation.Index H) (hom-presentation-not-subcountable H)

modal-subcountability-refutes-negative-small-homs : ModalAllSmallSubcountable
  → ¬ NN SmallHomPresentation
modal-subcountability-refutes-negative-small-homs sc n =
  n (modal-subcountability-refutes-small-homs sc)

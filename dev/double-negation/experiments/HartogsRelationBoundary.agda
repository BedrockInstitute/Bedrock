{-# OPTIONS --cubical --safe --guardedness #-}
module HartogsRelationBoundary where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma using (_×_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Bool using (false)
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Induction.WellFounded using (Acc; acc; WellFounded)
open import ModalTrees using (NN; mapNN)
open import BooleanCompletion using (StableProp; Holds)
open import RelationalTruth using (Pred; PredicateCover; truth-code)
open import SubcountableObstruction using (ModalAllSmallSubcountable;
  cover-index-not-subcountable)

module _ {ℓ : Level} (A : Type ℓ) where
  Carrier : Type ℓ
  Carrier = A ⊎ Unit

  record WellFoundedRelation : Type (ℓ-suc ℓ) where
    field
      relation : Carrier → Carrier → StableProp ℓ
      transitive : (x y z : Carrier) → Holds (relation x y)
        → Holds (relation y z) → Holds (relation x z)
      well-founded : WellFounded (λ x y → Holds (relation x y))

  Agree : WellFoundedRelation → WellFoundedRelation → Type ℓ
  Agree R S = (x y : Carrier) →
    (Holds (WellFoundedRelation.relation R x y)
      → Holds (WellFoundedRelation.relation S x y)) ×
    (Holds (WellFoundedRelation.relation S x y)
      → Holds (WellFoundedRelation.relation R x y))

  record RelationCover : Type (ℓ-suc ℓ) where
    field
      Index : Type ℓ
      family : Index → WellFoundedRelation
      covers : (R : WellFoundedRelation) → NN (Σ[ i ∈ Index ] Agree R (family i))

  height-two-relation : Pred A → Carrier → Carrier → StableProp ℓ
  height-two-relation P (inl a) (inr _) = P a
  height-two-relation P (inl a) (inl b) = truth-code false
  height-two-relation P (inr _) y = truth-code false

  no-below-left : (P : Pred A) (x : Carrier) (a : A)
    → Holds (height-two-relation P x (inl a)) → ⊥
  no-below-left P (inl x) a = Empty.rec*
  no-below-left P (inr _) a = Empty.rec*

  height-two-transitive : (P : Pred A) (x y z : Carrier)
    → Holds (height-two-relation P x y)
    → Holds (height-two-relation P y z)
    → Holds (height-two-relation P x z)
  height-two-transitive P x (inl a) z p q = Empty.rec (no-below-left P x a p)
  height-two-transitive P x (inr _) z p q = Empty.rec* q

  left-accessible : (P : Pred A) (a : A)
    → Acc (λ x y → Holds (height-two-relation P x y)) (inl a)
  left-accessible P a = acc (λ x p → Empty.rec (no-below-left P x a p))

  height-two-well-founded : (P : Pred A)
    → WellFounded (λ x y → Holds (height-two-relation P x y))
  height-two-well-founded P (inl a) = left-accessible P a
  height-two-well-founded P (inr _) = acc λ
    { (inl a) p → left-accessible P a
    ; (inr _) p → Empty.rec* p }

  height-two : Pred A → WellFoundedRelation
  WellFoundedRelation.relation (height-two P) = height-two-relation P
  WellFoundedRelation.transitive (height-two P) = height-two-transitive P
  WellFoundedRelation.well-founded (height-two P) = height-two-well-founded P

  relations-to-predicates : RelationCover → PredicateCover A
  PredicateCover.Index (relations-to-predicates cover) = RelationCover.Index cover
  PredicateCover.family (relations-to-predicates cover) i a =
    WellFoundedRelation.relation (RelationCover.family cover i) (inl a) (inr tt)
  PredicateCover.covers (relations-to-predicates cover) P = mapNN
    (λ { (i , agree) → i , λ a → agree (inl a) (inr tt) })
    (RelationCover.covers cover (height-two P))

modal-subcountability-refutes-relation-cover : ModalAllSmallSubcountable
  → ¬ RelationCover ℕ
modal-subcountability-refutes-relation-cover sc cover =
  sc (RelationCover.Index cover)
    (cover-index-not-subcountable (relations-to-predicates ℕ cover))

{-# OPTIONS --cubical --safe --guardedness #-}
module RelationalTruth where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma using (_×_)
open import Cubical.Data.Bool using (Bool; true; false; true≢false; false≢true)
open import Cubical.Data.Empty as Empty using (⊥; isProp⊥; ⊥*; isProp⊥*)
open import Cubical.Data.Unit using (Unit*; tt*; isPropUnit*)
open import Cubical.Relation.Nullary using (¬_; Dec; yes; no)
open import ModalTrees using (NN; mapNN)
open import BooleanPower using (pointwise-decision)
open import BooleanCompletion using (StableProp; Holds; stable-prop-ext;
  BooleanCompletion; evaluate; complete-truth; reconstruction)

module _ {ℓ : Level} where
  Classifies : StableProp ℓ → Bool → Type ℓ
  Classifies P true = Holds P
  Classifies P false = ¬ Holds P

  classification-prop : (P : StableProp ℓ) (b : Bool) → isProp (Classifies P b)
  classification-prop P true = P .fst .snd
  classification-prop P false = isPropΠ (λ _ → isProp⊥)

  classification-stable : (P : StableProp ℓ) (b : Bool)
    → NN (Classifies P b) → Classifies P b
  classification-stable P true = P .snd
  classification-stable P false n p = n (λ np → np p)

  classification-total : (P : StableProp ℓ) → NN (Σ[ b ∈ Bool ] Classifies P b)
  classification-total P = mapNN decide (pointwise-decision (Holds P))
    where
    decide : Dec (Holds P) → Σ[ b ∈ Bool ] Classifies P b
    decide (yes p) = true , p
    decide (no np) = false , np

  classification-unique : (P : StableProp ℓ) (b c : Bool)
    → Classifies P b → Classifies P c → b ≡ c
  classification-unique P true true _ _ = refl
  classification-unique P false false _ _ = refl
  classification-unique P true false p np = Empty.rec (np p)
  classification-unique P false true np p = Empty.rec (np p)

  truth-code : Bool → StableProp ℓ
  truth-code true = (Unit* , isPropUnit*) , (λ _ → tt*)
  truth-code false = (⊥* , isProp⊥*) , (λ n → Empty.rec (n Empty.rec*))

  code-classifies : (b : Bool) → Classifies (truth-code b) b
  code-classifies true = tt*
  code-classifies false = Empty.rec*

  inverse-unique : (P Q : StableProp ℓ) (b : Bool)
    → Classifies P b → Classifies Q b → P ≡ Q
  inverse-unique P Q true p q = stable-prop-ext P Q (λ _ → q) (λ _ → p)
  inverse-unique P Q false np nq = stable-prop-ext P Q
    (λ p → Empty.rec (np p)) (λ q → Empty.rec (nq q))

  classification-path : (P : StableProp ℓ) (b : Bool)
    → Classifies P b → P ≡ truth-code b
  classification-path P b c = inverse-unique P (truth-code b) b c (code-classifies b)

  code-dense : (P : StableProp ℓ) → NN (Σ[ b ∈ Bool ] P ≡ truth-code b)
  code-dense P = mapNN (λ { (b , c) → b , classification-path P b c })
    (classification-total P)

  module _ (A : Type ℓ) where
    RelBoolMap : Type (ℓ-suc ℓ)
    RelBoolMap = A → BooleanCompletion {ℓ}

    Pred : Type (ℓ-suc ℓ)
    Pred = A → StableProp ℓ

    PredAgree : Pred → Pred → Type ℓ
    PredAgree P Q = (a : A) → (Holds (P a) → Holds (Q a)) × (Holds (Q a) → Holds (P a))

    RelAgree : RelBoolMap → RelBoolMap → Type ℓ
    RelAgree R S = (a : A) (b : Bool) →
      (Holds (R a .fst b) → Holds (S a .fst b)) ×
      (Holds (S a .fst b) → Holds (R a .fst b))

    predicate-map : Pred → RelBoolMap
    predicate-map P a = complete-truth (P a)

    map-predicate : RelBoolMap → Pred
    map-predicate R a = evaluate (R a)

    predicate-map-agree : (P Q : Pred) → PredAgree P Q
      → RelAgree (predicate-map P) (predicate-map Q)
    predicate-map-agree P Q agree a true = agree a
    predicate-map-agree P Q agree a false =
      (λ np q → np (agree a .snd q)) , (λ nq p → nq (agree a .fst p))

    record PredicateCover : Type (ℓ-suc ℓ) where
      field
        Index : Type ℓ
        family : Index → Pred
        covers : (P : Pred) → NN (Σ[ i ∈ Index ] PredAgree P (family i))

    record FunctionCover : Type (ℓ-suc ℓ) where
      field
        Index : Type ℓ
        family : Index → RelBoolMap
        covers : (R : RelBoolMap) → NN (Σ[ i ∈ Index ] RelAgree R (family i))

    functions-to-predicates : FunctionCover → PredicateCover
    PredicateCover.Index (functions-to-predicates C) = FunctionCover.Index C
    PredicateCover.family (functions-to-predicates C) i = map-predicate (FunctionCover.family C i)
    PredicateCover.covers (functions-to-predicates C) P = mapNN
      (λ { (i , agree) → i , λ a → agree a true })
      (FunctionCover.covers C (predicate-map P))

    predicates-to-functions : PredicateCover → FunctionCover
    FunctionCover.Index (predicates-to-functions C) = PredicateCover.Index C
    FunctionCover.family (predicates-to-functions C) i = predicate-map (PredicateCover.family C i)
    FunctionCover.covers (predicates-to-functions C) R = mapNN
      (λ { (i , agree) → i , subst (λ S → RelAgree S
        (predicate-map (PredicateCover.family C i)))
        (funExt (λ a → reconstruction (R a)))
        (predicate-map-agree (map-predicate R) (PredicateCover.family C i) agree) })
      (PredicateCover.covers C (map-predicate R))

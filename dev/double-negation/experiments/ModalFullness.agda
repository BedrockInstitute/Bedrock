{-# OPTIONS --cubical --safe --guardedness #-}
module ModalFullness where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Sigma using (_×_)
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Relation.Nullary using (¬_)
open import ModalTrees using (NN; unitNN; mapNN)
open import BooleanCompletion using (StableProp; Holds; BooleanCompletion; complete-truth)
open import RelationalTruth using (RelBoolMap; RelAgree; FunctionCover)
open import SubcountableObstruction using (ModalAllSmallSubcountable;
  modal-subcountability-refutes-functions)

module _ {ℓ : Level} (A : Type ℓ) where
  record TotalRelation : Type (ℓ-suc ℓ) where
    field
      at : A → Bool → StableProp ℓ
      total : (a : A) → NN (Σ[ b ∈ Bool ] Holds (at a b))

  Refines : TotalRelation → TotalRelation → Type ℓ
  Refines S R = (a : A) (b : Bool) → Holds (TotalRelation.at S a b)
    → Holds (TotalRelation.at R a b)

  SingleValued : TotalRelation → Type ℓ
  SingleValued R = (a : A) (b c : Bool)
    → Holds (TotalRelation.at R a b) → Holds (TotalRelation.at R a c) → b ≡ c

  record BinaryFullness : Type (ℓ-suc ℓ) where
    field
      Index : Type ℓ
      family : Index → TotalRelation
      cofinal : (R : TotalRelation) → NN (Σ[ i ∈ Index ] Refines (family i) R)

  underlying : RelBoolMap A → TotalRelation
  TotalRelation.at (underlying R) a = R a .fst
  TotalRelation.total (underlying R) a = R a .snd .fst

  underlying-single : (R : RelBoolMap A) → SingleValued (underlying R)
  underlying-single R a b c = R a .snd .snd b c

  functionalize : (R : TotalRelation) → SingleValued R → RelBoolMap A
  functionalize R single a = TotalRelation.at R a , TotalRelation.total R a , single a

  module _ (full : BinaryFullness) where
    open BinaryFullness full

    refinement-single : (R : RelBoolMap A) (i : Index)
      → Refines (family i) (underlying R) → SingleValued (family i)
    refinement-single R i sub a b c pb pc = underlying-single R a b c
      (sub a b pb) (sub a c pc)

    refinement-agrees : (R : RelBoolMap A) (i : Index)
      → (sub : Refines (family i) (underlying R))
      → RelAgree A R (functionalize (family i) (refinement-single R i sub))
    refinement-agrees R i sub a b =
      (λ rb → TotalRelation.at (family i) a b .snd (mapNN
        (λ { (c , sc) → subst (λ d → Holds (TotalRelation.at (family i) a d))
          (underlying-single R a c b (sub a c sc) rb) sc })
        (TotalRelation.total (family i) a))) ,
      sub a b

    fullness-to-cover : FunctionCover A
    FunctionCover.Index fullness-to-cover = Σ[ i ∈ Index ] SingleValued (family i)
    FunctionCover.family fullness-to-cover (i , single) = functionalize (family i) single
    FunctionCover.covers fullness-to-cover R = mapNN
      (λ { (i , sub) → (i , refinement-single R i sub) , refinement-agrees R i sub })
      (cofinal (underlying R))

  choose-subfunction : TotalRelation → RelBoolMap A
  choose-subfunction R a = complete-truth (TotalRelation.at R a true)

  chosen-refines : (R : TotalRelation) → Refines (underlying (choose-subfunction R)) R
  chosen-refines R a true value = value
  chosen-refines R a false negative = TotalRelation.at R a false .snd
    (mapNN step (TotalRelation.total R a))
    where
    step : (Σ[ b ∈ Bool ] Holds (TotalRelation.at R a b))
      → Holds (TotalRelation.at R a false)
    step (true , value) = Empty.rec (negative value)
    step (false , value) = value

  cover-to-fullness : FunctionCover A → BinaryFullness
  BinaryFullness.Index (cover-to-fullness cover) = FunctionCover.Index cover
  BinaryFullness.family (cover-to-fullness cover) i = underlying (FunctionCover.family cover i)
  BinaryFullness.cofinal (cover-to-fullness cover) R = mapNN
    (λ { (i , agree) → i , λ a b value → chosen-refines R a b (agree a b .snd value) })
    (FunctionCover.covers cover (choose-subfunction R))

modal-subcountability-refutes-binary-fullness : ModalAllSmallSubcountable
  → ¬ BinaryFullness ℕ
modal-subcountability-refutes-binary-fullness sc full =
  modal-subcountability-refutes-functions sc (fullness-to-cover ℕ full)

{-# OPTIONS --cubical --safe --guardedness #-}
module ModalQuotient where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence using (hPropExt)
open import Cubical.Foundations.Structure
open import Cubical.Data.Empty using (⊥*) renaming (rec* to ⊥*-rec)
open import Cubical.Data.Unit using (Unit*; tt*)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Data.Sigma using (_×_; Σ≡Prop)
open import Cubical.Relation.Binary.Base using (module BinaryRelation)
open BinaryRelation using (isEquivRel; equivRel)
import Cubical.HITs.SetQuotients as Q
open import ModalTrees

module _ {ℓ : Level} where
  S : Type (ℓ-suc ℓ)
  S = Tree ℓ Q./ Eq

  eq-equiv : isEquivRel (Eq {ℓ})
  eq-equiv = equivRel eq-refl eq-sym eq-trans

  membership : S → S → hProp ℓ
  membership = Q.rec2 isSetHProp
    (λ x a → Mem x a , mem-prop x a)
    (λ x y a e → Σ≡Prop (λ _ → isPropIsProp)
      (hPropExt (mem-prop x a) (mem-prop y a)
        (mem-left x y a e) (mem-left y x a (eq-sym x y e))))
    (λ x a b e → Σ≡Prop (λ _ → isPropIsProp)
      (hPropExt (mem-prop x a) (mem-prop x b)
        (mem-right x a b e) (mem-right x b a (eq-sym a b e))))

  extensionalityQ : (a b : S)
    → ((x : S) → (⟨ membership x a ⟩ → ⟨ membership x b ⟩)
                   × (⟨ membership x b ⟩ → ⟨ membership x a ⟩))
    → a ≡ b
  extensionalityQ = Q.elimProp2
    (λ a b → isPropΠ (λ _ → Q.squash/ a b))
    (λ a b ext → Q.eq/ a b (extensionality a b (λ x → ext Q.[ x ])))

  equality-stable : (a b : S) → NN (a ≡ b) → a ≡ b
  equality-stable = Q.elimProp2
    (λ a b → isPropΠ (λ _ → Q.squash/ a b))
    (λ a b n → Q.eq/ a b (eq-stable a b
      (mapNN (Q.effective eq-prop eq-equiv a b) n)))

  membership-stable : (x a : S) → NN ⟨ membership x a ⟩ → ⟨ membership x a ⟩
  membership-stable = Q.elimProp2
    (λ x a → isPropΠ (λ _ → membership x a .snd))
    mem-stable

  emptyTree : Tree ℓ
  emptyTree = sup ⊥* ⊥*-rec

  oneTree : Tree ℓ
  oneTree = sup Unit* (λ _ → emptyTree)

  empty-not-one : ¬ (Q.[ emptyTree ] ≡ Q.[ oneTree ])
  empty-not-one p = Q.effective eq-prop eq-equiv emptyTree oneTree p .snd tt*
    (λ z → ⊥*-rec (z .fst))

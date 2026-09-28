{-# OPTIONS --cubical --safe --guardedness #-}
module UniqueExtraction where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma using (Σ≡Prop)
open import ModalTrees using (NN; mapNN)

module _ {ℓ : Level} (C : Type ℓ) where
  DenseExtension : Type (ℓ-suc ℓ)
  DenseExtension = (D : hProp ℓ) → NN (D .fst) → (g : D .fst → C)
    → Σ[ c ∈ C ] ((d : D .fst) → c ≡ g d)

  UniqueExtraction : Type (ℓ-suc ℓ)
  UniqueExtraction = (R : C → hProp ℓ)
    → ((c : C) → NN (R c .fst) → R c .fst)
    → ((c d : C) → R c .fst → R d .fst → c ≡ d)
    → NN (Σ[ c ∈ C ] R c .fst)
    → Σ[ c ∈ C ] R c .fst

  extension-to-extraction : DenseExtension → UniqueExtraction
  extension-to-extraction extend R stable unique inhabited =
    point .fst , stable (point .fst) (mapNN recover inhabited)
    where
    D : Type ℓ
    D = Σ[ c ∈ C ] R c .fst

    propD : isProp D
    propD (c , rc) (d , rd) = Σ≡Prop (λ x → R x .snd) (unique c d rc rd)

    point : Σ[ c ∈ C ] ((d : D) → c ≡ d .fst)
    point = extend (D , propD) inhabited fst

    recover : D → R (point .fst) .fst
    recover d = subst (λ c → R c .fst) (sym (point .snd d)) (d .snd)

  module _ (setC : isSet C)
    (stable-equality : (c d : C) → NN (c ≡ d) → c ≡ d) where

    extraction-to-extension : UniqueExtraction → DenseExtension
    extraction-to-extension extract D inhabited g = extract R stable unique exists
      where
      R : C → hProp ℓ
      R c = ((d : D .fst) → c ≡ g d) , isPropΠ (λ d → setC c (g d))

      stable : (c : C) → NN (R c .fst) → R c .fst
      stable c n d = stable-equality c (g d) (mapNN (λ h → h d) n)

      unique : (c c' : C) → R c .fst → R c' .fst → c ≡ c'
      unique c c' h h' = stable-equality c c'
        (mapNN (λ d → h d ∙ sym (h' d)) inhabited)

      exists : NN (Σ[ c ∈ C ] R c .fst)
      exists = mapNN (λ d → g d , λ d' → cong g (D .snd d d')) inhabited

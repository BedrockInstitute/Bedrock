{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile
import CodedVocabulary
import K4.Algebra
import K4.Implication
import K5.Frame
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT

module K9.BooleanSeparation
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
    → ZFStructure._≈ˢ_ 𝒮 x y ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  (carrier order B : ZFStructure.S 𝒮)
  (L : K4.Algebra.Lattice 𝒮 B)
  (Cm : K4.Algebra.Complement 𝒮 B L)
  (Kc : K4.Algebra.CodedComplete 𝒮 B L)
  (fb : K5.Frame.Poset.ForcingBase 𝒮 carrier order B L Cm)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open PT using ( ∣_∣₁ )
open K4.Algebra 𝒮 using ( Pt; isSetPt; _≤ᴮ_; ⊆ˢ-trans )
open K4.Algebra.Lattice L
open K4.Algebra.Complement Cm using ( ¬ᴮ_ )
open K4.Implication 𝒮 ext paths B L Cm
  using ( ≤ᴮ-antisym; ⊓-comm; ⊓-⊤; ⊥-as-≤; ⊓⊥→≤¬; ≤-both-⊥ )
open CodedVocabulary 𝒮 using ( denseΔ )

module FP = K5.Frame.Poset 𝒮 carrier order
module FF = FP.Forcing ext paths B L Cm Kc fb
open FP using ( Cond; _≼ᶜ_ )
open K5.Frame.Poset.ForcingBase fb using ( i; i-dense; i-nonzero )
open FF using ( _⊩ᴮ_; ⊩ᴮ-intro; ⊩ᴮ-elim; ⊩ᴮ-reg; DenseBelow )

all-force-top : LEM ℓ → (b : Pt B)
  → ((p : Cond) → ⟨ p ⊩ᴮ b ⟩) → b ≡ ⊤ᴮ
all-force-top lem b all with lem ((¬ᴮ b ≡ ⊥ᴮ) , isSetPt B _ _)
... | inl zero-neg = ≤ᴮ-antisym (⊤-greatest b)
  (⊥-as-≤ ⊤ᴮ b (⊓-comm ⊤ᴮ (¬ᴮ b) ∙ ⊓-⊤ (¬ᴮ b) ∙ zero-neg))
... | inr nonzero-neg = Empty.rec (PT.rec Empty.isProp⊥ contradict
  (i-dense (¬ᴮ b) (λ e → Empty.rec (nonzero-neg e))))
  where
  contradict : Σ[ p ∈ Cond ] ⟨ i p ≤ᴮ (¬ᴮ b) ⟩ → Empty.⊥
  contradict (p , below-neg) = Empty.rec* (i-nonzero p
    (≤-both-⊥ (i p) b (⊩ᴮ-elim p b (all p)) below-neg))

module Atomic
  (eq mem : S → S → Pt B)
  (eq-sym : (a b : S) → eq a b ≡ eq b a)
  (mem-congʳ : (x a b : S)
    → ⟨ ((eq a b) ⊓ᴮ (mem x a)) ≤ᴮ mem x b ⟩)
  where

  separates : (p : Cond) (x a b : S)
    → ⟨ p ⊩ᴮ mem x a ⟩ → ⟨ p ⊩ᴮ (¬ᴮ (mem x b)) ⟩
    → ⟨ p ⊩ᴮ (¬ᴮ (eq a b)) ⟩
  separates p x a b yes no = ⊩ᴮ-intro p (¬ᴮ (eq a b))
    (⊓⊥→≤¬ (i p) (eq a b)
      (≤-both-⊥ ((i p) ⊓ᴮ (eq a b)) (mem x b) present absent))
    where
    present : ⟨ ((i p) ⊓ᴮ (eq a b)) ≤ᴮ mem x b ⟩
    present = ⊆ˢ-trans
      (⊓-glb (eq a b) (mem x a) ((i p) ⊓ᴮ (eq a b))
        (⊓-lb₂ (i p) (eq a b))
        (⊆ˢ-trans (⊓-lb₁ (i p) (eq a b)) (⊩ᴮ-elim p (mem x a) yes)))
      (mem-congʳ x a b)

    absent : ⟨ ((i p) ⊓ᴮ (eq a b)) ≤ᴮ (¬ᴮ (mem x b)) ⟩
    absent = ⊆ˢ-trans (⊓-lb₁ (i p) (eq a b))
      (⊩ᴮ-elim p (¬ᴮ (mem x b)) no)

  SeparationAt : Cond → S → S → S → Ω
  SeparationAt p x a b =
    ((p ⊩ᴮ mem x a) ⊓ (p ⊩ᴮ (¬ᴮ (mem x b)))) ⊔
    ((p ⊩ᴮ mem x b) ⊓ (p ⊩ᴮ (¬ᴮ (mem x a))))

  separation-forces : (p : Cond) (x a b : S)
    → ⟨ SeparationAt p x a b ⟩ → ⟨ p ⊩ᴮ (¬ᴮ (eq a b)) ⟩
  separation-forces p x a b = PT.rec (snd (p ⊩ᴮ (¬ᴮ (eq a b)))) cases
    where
    cases : (⟨ p ⊩ᴮ mem x a ⟩ × ⟨ p ⊩ᴮ (¬ᴮ (mem x b)) ⟩) ⊎
            (⟨ p ⊩ᴮ mem x b ⟩ × ⟨ p ⊩ᴮ (¬ᴮ (mem x a)) ⟩)
          → ⟨ p ⊩ᴮ (¬ᴮ (eq a b)) ⟩
    cases (inl (yes , no)) = separates p x a b yes no
    cases (inr (yes , no)) = subst (λ v → ⟨ p ⊩ᴮ (¬ᴮ v) ⟩)
      (eq-sym b a) (separates p x b a yes no)

  module Checked (check : S → S) (w : S) where

    Separating : Cond → S → S → Ω
    Separating p a b = ⋁ S (λ n → (n ∈ˢ w) ⊓ SeparationAt p (check n) a b)

    separating-forces : (p : Cond) (a b : S)
      → ⟨ Separating p a b ⟩ → ⟨ p ⊩ᴮ (¬ᴮ (eq a b)) ⟩
    separating-forces p a b = PT.rec (snd (p ⊩ᴮ (¬ᴮ (eq a b))))
      (λ { (n , hn , separate) → separation-forces p (check n) a b separate })

    dense-separation-forces : (a b : S) (p : Cond)
      → ⟨ DenseBelow p (λ q → Separating q a b) ⟩
      → ⟨ p ⊩ᴮ (¬ᴮ (eq a b)) ⟩
    dense-separation-forces a b p dense = ⊩ᴮ-reg p (¬ᴮ (eq a b))
      (λ q hqp → PT.map
        (λ { (r , hrq , separate) → r , hrq , separating-forces r a b separate })
        (dense q hqp))

    coded-dense-forces : (d a b : S)
      → ⟨ denseΔ carrier order d ⟩
      → ((q : Cond) → ⟨ fst q ∈ˢ d ⟩ → ⟨ Separating q a b ⟩)
      → ((r : S) → ⟨ r ∈ˢ d ⟩ → ⟨ r ∈ˢ carrier ⟩)
      → (p : Cond) → ⟨ p ⊩ᴮ (¬ᴮ (eq a b)) ⟩
    coded-dense-forces d a b dense separate inside p = dense-separation-forces a b p
      (λ q hqp → PT.map
        (λ { (r , hrd , hrq) →
          (r , inside r hrd) , hrq , separate (r , inside r hrd) hrd })
        (dense (fst q) (snd q)))

    coded-dense-top : LEM ℓ → (d a b : S)
      → ⟨ denseΔ carrier order d ⟩
      → ((q : Cond) → ⟨ fst q ∈ˢ d ⟩ → ⟨ Separating q a b ⟩)
      → ((r : S) → ⟨ r ∈ˢ d ⟩ → ⟨ r ∈ˢ carrier ⟩)
      → (¬ᴮ (eq a b)) ≡ ⊤ᴮ
    coded-dense-top lem d a b dense separate inside =
      all-force-top lem (¬ᴮ (eq a b))
        (coded-dense-forces d a b dense separate inside)

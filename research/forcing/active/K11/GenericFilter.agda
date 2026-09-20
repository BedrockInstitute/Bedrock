{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile
import CodedCompletion

module K11.GenericFilter
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (sep : OrdinaryProfile.Separation 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
         → ZFStructure._≈ˢ_ 𝒮 x y ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  (𝔓 : CodedCompletion.Presentation 𝒮)
  (laws : CodedCompletion.Coded.ForcingLaws 𝒮 𝔓)
  (lem : LEM ℓ)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Data.Nat.Properties using ( +-comm )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )
import K11.LeastIndex

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

module K = CodedCompletion.Core 𝒮 ext pow sep paths 𝔓 laws
open CodedCompletion.Coded 𝒮 𝔓 using ( _≼ᴵ_ )
module FS = K.FS
open FS using ( Cond ; Sub ; _≼_ ; ≼-refl ; ≼-trans ; _∈ᴾ_ ; isFilter )
module LI = K11.LeastIndex lem
open LI using ( Least ; leastOf )

module FromEnumerations
  (condEnum : ℕ → Cond)
  (condCover : (p : Cond) → Σ[ n ∈ ℕ ] (condEnum n ≡ p))
  (denseEnum : ℕ → S)
  (dense-dense : (n : ℕ) → ⟨ K.denseᴵ (denseEnum n) ⟩)
  (dense-sub : (n : ℕ) → ⟨ K.subsetOf (denseEnum n) ⟩)
  (denseCover : (d : S) → ⟨ K.subsetOf d ⟩ → ⟨ K.denseᴵ d ⟩
               → Σ[ n ∈ ℕ ] (denseEnum n ≡ d))
  where

  candidate : ℕ → ℕ → Cond → Ω
  candidate k j c = (condEnum j ≼ c) ⊓ (fst (condEnum j) ∈ˢ denseEnum k)

  candidates-exist : (k : ℕ) (c : Cond)
    → PT.∥ Σ[ j ∈ ℕ ] ⟨ candidate k j c ⟩ ∥₁
  candidates-exist k c = PT.map into (dense-dense k (fst c) (snd c))
    where
    at-cond : Cond → Ω
    at-cond z = (z ≼ c) ⊓ (fst z ∈ˢ denseEnum k)
    into : (Σ[ p ∈ S ] (⟨ p ∈ˢ denseEnum k ⟩ × ⟨ p ≼ᴵ fst c ⟩))
         → Σ[ j ∈ ℕ ] ⟨ candidate k j c ⟩
    into (p , hpd , hpq) =
      fst ic , subst (λ z → ⟨ at-cond z ⟩) (sym (snd ic)) (hpq , hpd)
      where
      ic : Σ[ i ∈ ℕ ] (condEnum i ≡ (p , dense-sub k p hpd))
      ic = condCover (p , dense-sub k p hpd)

  step-data : (k : ℕ) (c : Cond) → Least (λ j → candidate k j c)
  step-data k c = leastOf (λ j → candidate k j c) (candidates-exist k c)

  step : ℕ → Cond → Cond
  step k c = condEnum (fst (step-data k c))

  step-properties : (k : ℕ) (c : Cond)
    → (⟨ step k c ≼ c ⟩ × ⟨ fst (step k c) ∈ˢ denseEnum k ⟩)
  step-properties k c = fst (snd (step-data k c))

  chain : ℕ → Cond
  chain zero = condEnum zero
  chain (suc n) = step n (chain n)

  chain-decl : (n : ℕ) → ⟨ chain (suc n) ≼ chain n ⟩
  chain-decl n = fst (step-properties n (chain n))

  chain-at : (k n : ℕ) → ⟨ chain (k + n) ≼ chain n ⟩
  chain-at zero n = ≼-refl (chain n)
  chain-at (suc k) n = ≼-trans {p = chain (suc (k + n))}
    {q = chain (k + n)} {r = chain n} (chain-decl (k + n)) (chain-at k n)

  genericSet : Sub
  genericSet q = PT.∥ Σ[ n ∈ ℕ ] ⟨ chain n ≼ q ⟩ ∥₁ , PT.squash₁

  directed : (p q : Cond) → ⟨ p ∈ᴾ genericSet ⟩ → ⟨ q ∈ᴾ genericSet ⟩
    → ⟨ ⋁ Cond (λ r → (r ∈ᴾ genericSet) ⊓ ((r ≼ p) ⊓ (r ≼ q))) ⟩
  directed p q hp hq =
    PT.rec (snd goal)
      (λ { (m , hm) → PT.rec (snd goal) (λ { (n , hn) → at m n hm hn }) hq }) hp
    where
    goal : Ω
    goal = ⋁ Cond (λ r → (r ∈ᴾ genericSet) ⊓ ((r ≼ p) ⊓ (r ≼ q)))
    at : (m n : ℕ) → ⟨ chain m ≼ p ⟩ → ⟨ chain n ≼ q ⟩ → ⟨ goal ⟩
    at m n hm hn =
      ∣ chain (m + n)
      , (∣ m + n , ≼-refl (chain (m + n)) ∣₁
      , ( ≼-trans {p = chain (m + n)} {q = chain m} {r = p}
            (subst (λ z → ⟨ chain z ≼ chain m ⟩) (+-comm n m) (chain-at n m)) hm
        , ≼-trans {p = chain (m + n)} {q = chain n} {r = q} (chain-at m n) hn )) ∣₁

  genericFilter : isFilter genericSet
  genericFilter = record
    { inhabited = ∣ chain zero , ∣ zero , ≼-refl (chain zero) ∣₁ ∣₁
    ; upward = λ p q hp hq →
        PT.rec (snd (q ∈ᴾ genericSet))
          (λ { (m , hm) → ∣ m , ≼-trans {p = chain m} {q = p} {r = q} hm hq ∣₁ }) hp
    ; directed = directed }

  generic-meets : (d : S) → ⟨ K.subsetOf d ⟩ → ⟨ K.denseᴵ d ⟩
    → ⟨ ⋁ Cond (λ p → (p ∈ᴾ genericSet) ⊓ (fst p ∈ˢ d)) ⟩
  generic-meets d sub dn with denseCover d sub dn
  ... | (k , e) =
    ∣ chain (suc k) , (∣ suc k , ≼-refl (chain (suc k)) ∣₁ , hit-d ) ∣₁
    where
    hit-d : ⟨ fst (chain (suc k)) ∈ˢ d ⟩
    hit-d = subst (λ z → ⟨ fst (chain (suc k)) ∈ˢ z ⟩) e
      (snd (step-properties k (chain k)))

  generic : K.isGeneric genericSet
  generic = record { filter = genericFilter ; meets = generic-meets }

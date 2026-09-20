{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile
import CodedCompletion
import K11.GenericFilter

module K11.CountableGround
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
open import OrdinaryProfile 𝒮 using ( module PathRealization )
open PathRealization paths using ( ≈ˢ-to-path )
import Cubical.Data.Empty as Empty
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Data.Sum using ( _⊎_ ; inl ; inr )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )
import K11.LeastIndex

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

module K = CodedCompletion.Core 𝒮 ext pow sep paths 𝔓 laws
open CodedCompletion.Coded 𝒮 𝔓 using ( carrier )
module FS = K.FS
open FS using ( Cond ; Sub )
module LI = K11.LeastIndex lem
open LI using ( Least ; leastOf )

module FromCarrier
  (ν : ℕ → S)
  (ν-covers : (x : S) → PT.∥ Σ[ n ∈ ℕ ] ⟨ ν n ≈ˢ x ⟩ ∥₁)
  (base : Cond)
  where

  codeData : (x : S) → Least (λ n → ν n ≈ˢ x)
  codeData x = leastOf (λ n → ν n ≈ˢ x) (ν-covers x)

  codeIndex : S → ℕ
  codeIndex x = fst (codeData x)

  codeHit : (x : S) → ⟨ ν (codeIndex x) ≈ˢ x ⟩
  codeHit x = fst (snd (codeData x))

  codePath : (x : S) → ν (codeIndex x) ≡ x
  codePath x = ≈ˢ-to-path (ν (codeIndex x)) x (codeHit x)

  condEnum : ℕ → Cond
  condEnum n with lem (ν n ∈ˢ carrier)
  ... | inl h = ν n , h
  ... | inr _ = base

  condEnum-≡ : (n : ℕ) (h : ⟨ ν n ∈ˢ carrier ⟩) → condEnum n ≡ (ν n , h)
  condEnum-≡ n h with lem (ν n ∈ˢ carrier)
  ... | inl _ = Σ≡Prop (λ z → snd (z ∈ˢ carrier)) refl
  ... | inr hn = Empty.rec (hn h)

  condCover : (p : Cond) → Σ[ n ∈ ℕ ] (condEnum n ≡ p)
  condCover p with lem (ν (codeIndex (fst p)) ∈ˢ carrier)
  ... | inl h =
    codeIndex (fst p) ,
    condEnum-≡ (codeIndex (fst p)) h
      ∙ Σ≡Prop (λ z → snd (z ∈ˢ carrier)) (codePath (fst p))
  ... | inr hn =
    Empty.rec (hn (subst (λ z → ⟨ z ∈ˢ carrier ⟩) (sym (codePath (fst p))) (snd p)))

  dense-yes : S → Ω
  dense-yes d = K.denseᴵ d ⊓ K.subsetOf d

  denseEnum : ℕ → S
  denseEnum n with lem (dense-yes (ν n))
  ... | inl _ = ν n
  ... | inr _ = carrier

  denseEnum-≡ : (n : ℕ) (dyes : ⟨ dense-yes (ν n) ⟩) → denseEnum n ≡ ν n
  denseEnum-≡ n dyes with lem (dense-yes (ν n))
  ... | inl _ = refl
  ... | inr hn = Empty.rec (hn dyes)

  carrier-dense : ⟨ K.denseᴵ carrier ⟩
  carrier-dense q hq = ∣ q , hq , K.refl≼ q hq ∣₁

  dense-dense : (n : ℕ) → ⟨ K.denseᴵ (denseEnum n) ⟩
  dense-dense n with lem (dense-yes (ν n))
  ... | inl dyes = fst dyes
  ... | inr _ = carrier-dense

  dense-sub : (n : ℕ) → ⟨ K.subsetOf (denseEnum n) ⟩
  dense-sub n with lem (dense-yes (ν n))
  ... | inl dyes = snd dyes
  ... | inr _ = λ z hz → hz

  denseCover : (d : S) → ⟨ K.subsetOf d ⟩ → ⟨ K.denseᴵ d ⟩
    → Σ[ n ∈ ℕ ] (denseEnum n ≡ d)
  denseCover d sub dn with lem (dense-yes (ν (codeIndex d)))
  ... | inl dyes =
    codeIndex d , denseEnum-≡ (codeIndex d) dyes ∙ codePath d
  ... | inr hn =
    Empty.rec (hn ( subst (λ z → ⟨ K.denseᴵ z ⟩) (sym (codePath d)) dn
                  , subst (λ z → ⟨ K.subsetOf z ⟩) (sym (codePath d)) sub ))

  private
    module GEN = K11.GenericFilter 𝒮 ext pow sep paths 𝔓 laws lem
  module GF = GEN.FromEnumerations condEnum condCover denseEnum dense-dense
    dense-sub denseCover

carrier-generic : (ν : ℕ → S)
  → ((x : S) → PT.∥ Σ[ n ∈ ℕ ] ⟨ ν n ≈ˢ x ⟩ ∥₁)
  → (base : Cond) → Σ[ G ∈ Sub ] K.isGeneric G
carrier-generic ν ν-covers base = result
  where
  module FC = FromCarrier ν ν-covers base
  result : Σ[ G ∈ Sub ] K.isGeneric G
  result = FC.GF.genericSet , FC.GF.generic

generic-truncated : (base : Cond)
  → PT.∥ Σ[ ν ∈ (ℕ → S) ] ((x : S) → PT.∥ Σ[ n ∈ ℕ ] ⟨ ν n ≈ˢ x ⟩ ∥₁) ∥₁
  → PT.∥ Σ[ G ∈ Sub ] K.isGeneric G ∥₁
generic-truncated base =
  PT.rec PT.squash₁ (λ { (ν , covers) → ∣ carrier-generic ν covers base ∣₁ })

{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile
import CardinalBridge

module K9.GenericBits
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
    → ZFStructure._≈ˢ_ 𝒮 x y ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  (pair : OrdinaryProfile.Pairing 𝒮)
  (un : OrdinaryProfile.Union 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (sep : OrdinaryProfile.Separation 𝒮)
  (find : OrdinaryProfile.FoundationInduction 𝒮)
  (κ w : ZFStructure.S 𝒮)
  (lem : LEM ℓ)
  (hw : ⟨ CardinalBridge.isOmega 𝒮 w ⟩)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import CodedVocabulary 𝒮 using ( isKPairΔ; refinesΔ )
import CodedCompletion
import K8.Cohen
import K8.DistinctDense
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

module C = K8.Cohen 𝒮 ext paths pair un pow sep κ w
  using ( bit₀; bit₁; two; bit₀-in; bit₁-in; bits-distinct
        ; coordinates; coordinate; coordinate-in; D; D-dense
        ; carrier; order; presentation; laws
        ; module GS; module PM; module PC; module MO; module CD )
module Completion = CodedCompletion.Core
  𝒮 ext pow sep paths C.presentation C.laws
  using ( subsetOf; isGeneric; module FS )
module Dense = K8.DistinctDense
  𝒮 ext paths pair un pow sep find κ w hw
  using ( E; E-spec; E-dense )

module AtGeneric
  (G : Completion.FS.Sub)
  (generic : Completion.isGeneric G)
  where

  open Completion.FS using ( Cond; _≼_; _∈ᴾ_; isFilter )

  Bit : S → S → S → Ω
  Bit α n b = ⋁ Cond (λ p → (p ∈ᴾ G) ⊓ refinesΔ (fst p) (C.coordinate α n) b)

  filter : isFilter G
  filter = Completion.isGeneric.filter generic

  bit-functional : (α n b c : S)
    → ⟨ α ∈ˢ κ ⟩ → ⟨ n ∈ˢ w ⟩
    → ⟨ b ∈ˢ C.two ⟩ → ⟨ c ∈ˢ C.two ⟩
    → ⟨ Bit α n b ⟩ → ⟨ Bit α n c ⟩ → ⟨ b ≈ˢ c ⟩
  bit-functional α n b c hα hn hb hc h h' =
    PT.rec (snd (b ≈ˢ c)) first h
    where
    x : S
    x = C.coordinate α n

    hx : ⟨ x ∈ˢ C.coordinates ⟩
    hx = C.coordinate-in α n hα hn

    first : Σ[ p ∈ Cond ] (⟨ p ∈ᴾ G ⟩ × ⟨ refinesΔ (fst p) x b ⟩)
      → ⟨ b ≈ˢ c ⟩
    first (p , hpG , pb) = PT.rec (snd (b ≈ˢ c)) second h'
      where
      second : Σ[ q ∈ Cond ] (⟨ q ∈ᴾ G ⟩ × ⟨ refinesΔ (fst q) x c ⟩)
        → ⟨ b ≈ˢ c ⟩
      second (q , hqG , qc) = PT.rec (snd (b ≈ˢ c)) common
        (isFilter.directed filter p q hpG hqG)
        where
        common : Σ[ r ∈ Cond ]
          (⟨ r ∈ᴾ G ⟩ ×
            (⟨ r ≼ p ⟩ × ⟨ r ≼ q ⟩))
          → ⟨ b ≈ˢ c ⟩
        common (r , _ , rp , rq) =
          snd (subst ⟨_⟩ (C.PM.carrier-spec (fst r)) (snd r))
            x hx b hb c hc
            ( C.MO.refines-mono (fst p) (fst r) x b
                (subst ⟨_⟩ (C.PC.refines-spec (fst r) (fst p) (snd r) (snd p)) rp)
                pb
            , C.MO.refines-mono (fst q) (fst r) x c
                (subst ⟨_⟩ (C.PC.refines-spec (fst r) (fst q) (snd r) (snd q)) rq)
                qc )

  bit-dichotomy : (b : S) → ⟨ b ∈ˢ C.two ⟩
    → ⟨ (b ≈ˢ C.bit₀) ⊔ (b ≈ˢ C.bit₁) ⟩
  bit-dichotomy b = C.GS.pairOf-out C.bit₀ C.bit₁ b

  coordinate-subset : (α n : S) → ⟨ Completion.subsetOf (C.D α n) ⟩
  coordinate-subset α n p hp =
    fst (subst ⟨_⟩ (C.CD.D-spec (C.coordinate α n) p) hp)

  bit-total : (α n : S) → ⟨ α ∈ˢ κ ⟩ → ⟨ n ∈ˢ w ⟩
    → ⟨ ⋁ S (λ b → (b ∈ˢ C.two) ⊓ Bit α n b) ⟩
  bit-total α n hα hn = PT.rec PT.isPropPropTrunc atCondition
    (Completion.isGeneric.meets generic (C.D α n)
      (coordinate-subset α n) (C.D-dense lem α n hα hn))
    where
    atCondition : Σ[ p ∈ Cond ]
      (⟨ p ∈ᴾ G ⟩ × ⟨ fst p ∈ˢ C.D α n ⟩)
      → ⟨ ⋁ S (λ b → (b ∈ˢ C.two) ⊓ Bit α n b) ⟩
    atCondition (p , hpG , hpD) = PT.map
      (λ { (b , hb , ev) → b , hb , ∣ p , hpG , ev ∣₁ })
      (snd (subst ⟨_⟩ (C.CD.D-spec (C.coordinate α n) (fst p)) hpD))

  bit-total₀₁ : (α n : S) → ⟨ α ∈ˢ κ ⟩ → ⟨ n ∈ˢ w ⟩
    → ⟨ Bit α n C.bit₀ ⊔ Bit α n C.bit₁ ⟩
  bit-total₀₁ α n hα hn = PT.rec PT.isPropPropTrunc choose
    (bit-total α n hα hn)
    where
    choose : Σ[ b ∈ S ] (⟨ b ∈ˢ C.two ⟩ × ⟨ Bit α n b ⟩)
      → ⟨ Bit α n C.bit₀ ⊔ Bit α n C.bit₁ ⟩
    choose (b , hb , hbit) = PT.map branch (bit-dichotomy b hb)
      where
      branch : ⟨ b ≈ˢ C.bit₀ ⟩ ⊎ ⟨ b ≈ˢ C.bit₁ ⟩
        → ⟨ Bit α n C.bit₀ ⟩ ⊎ ⟨ Bit α n C.bit₁ ⟩
      branch (inl e) = inl (subst (λ b → ⟨ Bit α n b ⟩) (C.GS.≈→≡ e) hbit)
      branch (inr e) = inr (subst (λ b → ⟨ Bit α n b ⟩) (C.GS.≈→≡ e) hbit)

  bits-exclusive : (α n : S) → ⟨ α ∈ˢ κ ⟩ → ⟨ n ∈ˢ w ⟩
    → ⟨ Bit α n C.bit₀ ⟩ → ⟨ Bit α n C.bit₁ ⟩ → ⟨ ⊥ ⟩
  bits-exclusive α n hα hn h₀ h₁ = C.bits-distinct
    (bit-functional α n C.bit₀ C.bit₁ hα hn C.bit₀-in C.bit₁-in h₀ h₁)

  distinct-subset : (α β : S) → ⟨ Completion.subsetOf (Dense.E α β) ⟩
  distinct-subset α β p hp = fst (subst ⟨_⟩ (Dense.E-spec α β p) hp)

  separatedBits : S → S → S → Ω
  separatedBits α β n = ⋁ S (λ b → (b ∈ˢ C.two) ⊓
    ⋁ S (λ c → (c ∈ˢ C.two) ⊓
      (Bit α n b ⊓ (Bit β n c ⊓ ((b ≈ˢ c) ⇒ ⊥)))))

  private
    unequalRight : S → S → S → S → Ω
    unequalRight p u v b = ⋁ S (λ c → (c ∈ˢ C.two) ⊓
      (refinesΔ p u b ⊓ (refinesΔ p v c ⊓ ((b ≈ˢ c) ⇒ ⊥))))

    unequalValues : S → S → S → Ω
    unequalValues p u v = ⋁ S (λ b → (b ∈ˢ C.two) ⊓ unequalRight p u v b)

    unequalSecond : S → S → S → S → S → Ω
    unequalSecond α β p n u = ⋁ S (λ v → (v ∈ˢ C.coordinates) ⊓
      (isKPairΔ u α n ⊓ (isKPairΔ v β n ⊓ unequalValues p u v)))

    unequalCoordinates : S → S → S → S → Ω
    unequalCoordinates α β p n = ⋁ S (λ u → (u ∈ˢ C.coordinates) ⊓
      unequalSecond α β p n u)

  distinct-bits : (α β : S)
    → ⟨ α ∈ˢ κ ⟩ → ⟨ β ∈ˢ κ ⟩
    → ⟨ (α ≈ˢ β) ⇒ ⊥ ⟩
    → ⟨ ⋁ S (λ n → (n ∈ˢ w) ⊓ separatedBits α β n) ⟩
  distinct-bits α β hα hβ α≠β = PT.rec PT.isPropPropTrunc atCondition
    (Completion.isGeneric.meets generic (Dense.E α β)
      (distinct-subset α β) (Dense.E-dense lem α β hα hβ α≠β))
    where
    atCondition : Σ[ p ∈ Cond ]
      (⟨ p ∈ᴾ G ⟩ × ⟨ fst p ∈ˢ Dense.E α β ⟩)
      → ⟨ ⋁ S (λ n → (n ∈ˢ w) ⊓ separatedBits α β n) ⟩
    atCondition (p , hpG , hpE) = PT.rec PT.isPropPropTrunc atNatural
      (snd (subst ⟨_⟩ (Dense.E-spec α β (fst p)) hpE))
      where
      atNatural : Σ[ n ∈ S ] (⟨ n ∈ˢ w ⟩ ×
        ⟨ unequalCoordinates α β (fst p) n ⟩)
        → ⟨ ⋁ S (λ n → (n ∈ˢ w) ⊓ separatedBits α β n) ⟩
      atNatural (n , hn , rest) = PT.rec PT.isPropPropTrunc atFirst rest
        where
        atFirst : Σ[ u ∈ S ] (⟨ u ∈ˢ C.coordinates ⟩ ×
          ⟨ unequalSecond α β (fst p) n u ⟩)
          → ⟨ ⋁ S (λ n → (n ∈ˢ w) ⊓ separatedBits α β n) ⟩
        atFirst (u , _ , tail) = PT.rec PT.isPropPropTrunc atSecond tail
          where
          atSecond : Σ[ v ∈ S ] (⟨ v ∈ˢ C.coordinates ⟩ ×
            (⟨ isKPairΔ u α n ⟩ ×
              (⟨ isKPairΔ v β n ⟩ × ⟨ unequalValues (fst p) u v ⟩)))
            → ⟨ ⋁ S (λ n → (n ∈ˢ w) ⊓ separatedBits α β n) ⟩
          atSecond (v , _ , ku , kv , values) =
            PT.rec PT.isPropPropTrunc atLeft values
            where
            atLeft : Σ[ b ∈ S ] (⟨ b ∈ˢ C.two ⟩ ×
              ⟨ unequalRight (fst p) u v b ⟩)
              → ⟨ ⋁ S (λ n → (n ∈ˢ w) ⊓ separatedBits α β n) ⟩
            atLeft (b , hb , right) = PT.rec PT.isPropPropTrunc atRight right
              where
              atRight : Σ[ c ∈ S ] (⟨ c ∈ˢ C.two ⟩ ×
                (⟨ refinesΔ (fst p) u b ⟩ ×
                  (⟨ refinesΔ (fst p) v c ⟩ × ⟨ (b ≈ˢ c) ⇒ ⊥ ⟩)))
                → ⟨ ⋁ S (λ n → (n ∈ˢ w) ⊓ separatedBits α β n) ⟩
              atRight (c , hc , pu , pv , neq) =
                ∣ n , hn , ∣ b , hb , ∣ c , hc ,
                  ∣ p , hpG , subst (λ x → ⟨ refinesΔ (fst p) x b ⟩)
                    (C.GS.ordered-unique u α n ku) pu ∣₁ ,
                  ∣ p , hpG , subst (λ x → ⟨ refinesΔ (fst p) x c ⟩)
                    (C.GS.ordered-unique v β n kv) pv ∣₁ , neq ∣₁ ∣₁ ∣₁

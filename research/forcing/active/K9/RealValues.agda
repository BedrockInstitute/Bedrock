{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile
import CardinalBridge

module K9.RealValues
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (families : NameKernel.Families 𝒮)
  (accessible : NameKernel.Accessibility 𝒮)
  (images : NameKernel.MemberImage 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (find : OrdinaryProfile.FoundationInduction 𝒮)
  (κ w : ZFStructure.S 𝒮)
  (lem : LEM ℓ)
  (hw : ⟨ CardinalBridge.isOmega 𝒮 w ⟩)
  where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.ZFModel
open import CodedVocabulary 𝒮 using ( refinesΔ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )
import K9.NameGround
import K9.RealNames
import K9.GenericBits

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

module NG = K9.NameGround 𝒮 families accessible images pow κ w
  using ( module GS; module C; module K; module Check; module PS; module P
        ; module AtGeneric
        ; extensional; hasPair; hasUnion; hasSeparation; ≈ˢ-paths )
module RN = K9.RealNames 𝒮 families accessible images pow κ w
  using ( realCode; real-spec; real; real-entry )
module GB = K9.GenericBits 𝒮 NG.extensional NG.≈ˢ-paths
  NG.hasPair NG.hasUnion pow NG.hasSeparation find κ w lem hw
  using ( module Completion; module AtGeneric )

module AtGeneric
  (G : NG.P.Sub)
  (generic : GB.Completion.isGeneric G)
  where

  module Ground = NG.AtGeneric G
  module E = Ground.E
  module CopyBase = Ground.Copy
  module Bits = GB.AtGeneric G generic
  module ExtensionModel = FOL.ZFModel NG.PS.𝒮ᴾ[ G ]
  open ExtensionModel using () renaming ( _⊆ˢ_ to _⊆ᴱ_ )
  open hPropStructure NG.PS.𝒮ᴾ[ G ]
    using () renaming ( _≈ˢ_ to _≈ᴱ_; _∈ˢ_ to _∈ᴱ_ )
  open E using ( ‖Active‖; entry-value; ≈-refl; ≈-sym; ∈-congˡ; ∈-congʳ )
    renaming ( _≈[G]_ to _≈ᵛ_; _∈[G]_ to _∈ᵛ_ )
  open NG.P using ( Cond; _∈ᴾ_ )

  filter : NG.P.isFilter G
  filter = GB.Completion.isGeneric.filter generic

  positive : ⟨ NG.P.positive G ⟩
  positive = NG.P.isFilter.inhabited filter

  module Copy = CopyBase.WithPos positive

  real-value-spec : (α χ : S) → (χ ∈ᵛ RN.realCode α) ≡
    ⋁ S (λ n → (n ∈ˢ w) ⊓
      (Bits.Bit α n NG.C.bit₁ ⊓ (χ ≈ᵛ NG.Check.chk n)))
  real-value-spec α χ = ⇔toPath forward backward
    where
    Target : Ω
    Target = ⋁ S (λ n → (n ∈ˢ w) ⊓
      (Bits.Bit α n NG.C.bit₁ ⊓ (χ ≈ᵛ NG.Check.chk n)))

    forward : ⟨ χ ∈ᵛ RN.realCode α ⟩ → ⟨ Target ⟩
    forward = PT.rec (snd Target) atMember
      where
      atMember : Σ[ y ∈ S ] (⟨ ‖Active‖ y (RN.realCode α) ⟩ × ⟨ χ ≈ᵛ y ⟩)
        → ⟨ Target ⟩
      atMember (y , active , equal) = PT.rec (snd Target) atActive active
        where
        atActive : Σ[ p ∈ S ] Σ[ hp ∈ ⟨ p ∈ˢ NG.C.carrier ⟩ ]
          (⟨ NG.K.entry y p ∈ˢ RN.realCode α ⟩ × ⟨ (p , hp) ∈ᴾ G ⟩)
          → ⟨ Target ⟩
        atActive (p , hp , member , hpG) = PT.rec (snd Target) atNatural
          (subst ⟨_⟩ (RN.real-spec α (NG.K.entry y p)) member)
          where
          atNatural : Σ[ n ∈ S ] (⟨ n ∈ˢ w ⟩ ×
            ⟨ ⋁ S (λ q → (q ∈ˢ NG.C.carrier) ⊓
              (refinesΔ q (NG.C.coordinate α n) NG.C.bit₁ ⊓
                (NG.K.entry y p ≈ˢ NG.K.entry (NG.Check.chk n) q))) ⟩)
            → ⟨ Target ⟩
          atNatural (n , hn , conditions) = PT.rec (snd Target) atCondition conditions
            where
            atCondition : Σ[ q ∈ S ] (⟨ q ∈ˢ NG.C.carrier ⟩ ×
              (⟨ refinesΔ q (NG.C.coordinate α n) NG.C.bit₁ ⟩ ×
                ⟨ NG.K.entry y p ≈ˢ NG.K.entry (NG.Check.chk n) q ⟩))
              → ⟨ Target ⟩
            atCondition (q , _ , bit , entryEqual) =
              ∣ n , hn , ∣ (p , hp) , hpG ,
                subst (λ r → ⟨ refinesΔ r
                  (NG.C.coordinate α n) NG.C.bit₁ ⟩)
                  (sym (snd components)) bit ∣₁ ,
                subst (λ z → ⟨ χ ≈ᵛ z ⟩) (fst components) equal ∣₁
              where
              components : (y ≡ NG.Check.chk n) × (p ≡ q)
              components = NG.K.entry-inj (NG.GS.≈→≡ entryEqual)

    backward : ⟨ Target ⟩ → ⟨ χ ∈ᵛ RN.realCode α ⟩
    backward = PT.rec (snd (χ ∈ᵛ RN.realCode α)) atNatural
      where
      atNatural : Σ[ n ∈ S ] (⟨ n ∈ˢ w ⟩ ×
        (⟨ Bits.Bit α n NG.C.bit₁ ⟩ × ⟨ χ ≈ᵛ NG.Check.chk n ⟩))
        → ⟨ χ ∈ᵛ RN.realCode α ⟩
      atNatural (n , hn , bit , equal) = PT.rec (snd (χ ∈ᵛ RN.realCode α))
        atCondition bit
        where
        atCondition : Σ[ p ∈ Cond ]
          (⟨ p ∈ᴾ G ⟩ ×
            ⟨ refinesΔ (fst p) (NG.C.coordinate α n) NG.C.bit₁ ⟩)
          → ⟨ χ ∈ᵛ RN.realCode α ⟩
        atCondition (p , hpG , evaluates) = ∈-congˡ (≈-sym equal)
          (entry-value (RN.realCode α) (NG.Check.chk n) (fst p) (snd p) hpG
            (RN.real-entry α n (fst p) hn (snd p) evaluates))

  real-membership-spec : (α : S) (χ : NG.PS.Nameᴾ)
    → (χ ∈ᴱ RN.real α) ≡ ⋁ S (λ n → (n ∈ˢ w) ⊓
      (Bits.Bit α n NG.C.bit₁ ⊓ (fst χ ≈ᵛ NG.Check.chk n)))
  real-membership-spec α χ = real-value-spec α (fst χ)

  real-subset-check : (α : S) → ⟨ RN.real α ⊆ᴱ CopyBase.groundName w ⟩
  real-subset-check α χ member = PT.rec (snd (χ ∈ᴱ CopyBase.groundName w))
    atNatural (subst ⟨_⟩ (real-membership-spec α χ) member)
    where
    atNatural : Σ[ n ∈ S ] (⟨ n ∈ˢ w ⟩ ×
      (⟨ Bits.Bit α n NG.C.bit₁ ⟩ × ⟨ fst χ ≈ᵛ NG.Check.chk n ⟩))
      → ⟨ χ ∈ᴱ CopyBase.groundName w ⟩
    atNatural (n , hn , _ , equal) = subst ⟨_⟩
      (sym (Copy.check-value w (fst χ))) ∣ n , hn , equal ∣₁

  checked-natural-membership : (α n : S) → ⟨ n ∈ˢ w ⟩
    → (CopyBase.groundName n ∈ᴱ RN.real α) ≡ Bits.Bit α n NG.C.bit₁
  checked-natural-membership α n hn = ⇔toPath forward backward
    where
    forward : ⟨ CopyBase.groundName n ∈ᴱ RN.real α ⟩
      → ⟨ Bits.Bit α n NG.C.bit₁ ⟩
    forward member = PT.rec (snd (Bits.Bit α n NG.C.bit₁)) atNatural
      (subst ⟨_⟩ (real-membership-spec α (CopyBase.groundName n)) member)
      where
      atNatural : Σ[ m ∈ S ] (⟨ m ∈ˢ w ⟩ ×
        (⟨ Bits.Bit α m NG.C.bit₁ ⟩ ×
          ⟨ NG.Check.chk n ≈ᵛ NG.Check.chk m ⟩))
        → ⟨ Bits.Bit α n NG.C.bit₁ ⟩
      atNatural (m , _ , bit , equal) =
        subst (λ k → ⟨ Bits.Bit α k NG.C.bit₁ ⟩)
          (sym (NG.GS.≈→≡ (Copy.check-≈-inj n m equal))) bit

    backward : ⟨ Bits.Bit α n NG.C.bit₁ ⟩
      → ⟨ CopyBase.groundName n ∈ᴱ RN.real α ⟩
    backward bit = subst ⟨_⟩
      (sym (real-membership-spec α (CopyBase.groundName n)))
      ∣ n , hn , bit , ≈-refl (NG.Check.chk n) ∣₁

  private
    ground-path : {x y : S} → x ≡ y → ⟨ x ≈ˢ y ⟩
    ground-path {x} {y} = subst ⟨_⟩ (sym (NG.≈ˢ-paths x y))

  real-values-distinct : (α β : S)
    → ⟨ α ∈ˢ κ ⟩ → ⟨ β ∈ˢ κ ⟩ → ⟨ (α ≈ˢ β) ⇒ ⊥ ⟩
    → ⟨ RN.real α ≈ᴱ RN.real β ⟩ → ⟨ ⊥ ⟩
  real-values-distinct α β hα hβ α≠β equal =
    PT.rec (snd ⊥) atNatural (Bits.distinct-bits α β hα hβ α≠β)
    where
    atNatural : Σ[ n ∈ S ] (⟨ n ∈ˢ w ⟩ × ⟨ Bits.separatedBits α β n ⟩)
      → ⟨ ⊥ ⟩
    atNatural (n , hn , separated) = PT.rec (snd ⊥) atLeft separated
      where
      atLeft : Σ[ b ∈ S ] (⟨ b ∈ˢ NG.C.two ⟩ ×
        ⟨ ⋁ S (λ c → (c ∈ˢ NG.C.two) ⊓
          (Bits.Bit α n b ⊓
            (Bits.Bit β n c ⊓ ((b ≈ˢ c) ⇒ ⊥)))) ⟩)
        → ⟨ ⊥ ⟩
      atLeft (b , hb , right) = PT.rec (snd ⊥) atRight right
        where
        atRight : Σ[ c ∈ S ] (⟨ c ∈ˢ NG.C.two ⟩ ×
          (⟨ Bits.Bit α n b ⟩ ×
            (⟨ Bits.Bit β n c ⟩ × ⟨ (b ≈ˢ c) ⇒ ⊥ ⟩)))
          → ⟨ ⊥ ⟩
        atRight (c , hc , bitA , bitB , unequal) = PT.rec (snd ⊥) atB
          (Bits.bit-dichotomy b hb)
          where
          atB : ⟨ b ≈ˢ NG.C.bit₀ ⟩ ⊎ ⟨ b ≈ˢ NG.C.bit₁ ⟩ → ⟨ ⊥ ⟩
          atB bCase = PT.rec (snd ⊥) (atC bCase) (Bits.bit-dichotomy c hc)
            where
            atC : ⟨ b ≈ˢ NG.C.bit₀ ⟩ ⊎ ⟨ b ≈ˢ NG.C.bit₁ ⟩
              → ⟨ c ≈ˢ NG.C.bit₀ ⟩ ⊎ ⟨ c ≈ˢ NG.C.bit₁ ⟩ → ⟨ ⊥ ⟩
            atC (inl b₀) (inl c₀) = unequal
              (ground-path (NG.GS.≈→≡ b₀ ∙ sym (NG.GS.≈→≡ c₀)))
            atC (inr b₁) (inr c₁) = unequal
              (ground-path (NG.GS.≈→≡ b₁ ∙ sym (NG.GS.≈→≡ c₁)))
            atC (inl b₀) (inr c₁) = Bits.bits-exclusive α n hα hn
              (subst (λ d → ⟨ Bits.Bit α n d ⟩) (NG.GS.≈→≡ b₀) bitA)
              (subst ⟨_⟩ (checked-natural-membership α n hn)
                (∈-congʳ (≈-sym equal)
                  (subst ⟨_⟩ (sym (checked-natural-membership β n hn))
                    (subst (λ d → ⟨ Bits.Bit β n d ⟩)
                      (NG.GS.≈→≡ c₁) bitB))))
            atC (inr b₁) (inl c₀) = Bits.bits-exclusive β n hβ hn
              (subst (λ d → ⟨ Bits.Bit β n d ⟩) (NG.GS.≈→≡ c₀) bitB)
              (subst ⟨_⟩ (checked-natural-membership β n hn)
                (∈-congʳ equal
                  (subst ⟨_⟩ (sym (checked-natural-membership α n hn))
                    (subst (λ d → ⟨ Bits.Bit α n d ⟩)
                      (NG.GS.≈→≡ b₁) bitA))))

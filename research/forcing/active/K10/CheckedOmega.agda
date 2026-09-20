{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile
import CardinalBridge

module K10.CheckedOmega
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (families : NameKernel.Families 𝒮)
  (accessible : NameKernel.Accessibility 𝒮)
  (images : NameKernel.MemberImage 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (κ w : ZFStructure.S 𝒮)
  (hw : ⟨ CardinalBridge.isOmega 𝒮 w ⟩)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.LevyHierarchy using ( Δ₀; checkΔ₀ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Unit using ( tt )
open import Cubical.Induction.WellFounded using ( module WFI )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
import K8.FiniteVocabulary
import K8.OmegaInduction
import K9.NameGround

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

module CBᴳ = CardinalBridge 𝒮
module NG = K9.NameGround 𝒮 families accessible images pow κ w
  using ( module Check; module P; module PS; module AtGeneric
        ; extensional; hasPair; hasUnion; hasSeparation; ≈ˢ-paths )
module FVᴳ = K8.FiniteVocabulary 𝒮
module OI = K8.OmegaInduction 𝒮 NG.extensional NG.≈ˢ-paths
  NG.hasPair NG.hasUnion pow NG.hasSeparation κ

Δ₀-IsInductiveφ : Δ₀ CBᴳ.IsInductiveφ
Δ₀-IsInductiveφ = checkΔ₀ CBᴳ.IsInductiveφ tt

Δ₀-IsSuccOfφ : Δ₀ CBᴳ.IsSuccOfφ
Δ₀-IsSuccOfφ = checkΔ₀ CBᴳ.IsSuccOfφ tt

module AtGeneric
  (G : NG.P.Sub)
  (positive : ⟨ NG.P.positive G ⟩)
  where

  module Ground = NG.AtGeneric G
  module E = Ground.E
  module CopyBase = Ground.Copy
  module Copy = CopyBase.WithPos positive
  module CBᴱ = CardinalBridge NG.PS.𝒮ᴾ[ G ]
  module FVᴱ = K8.FiniteVocabulary NG.PS.𝒮ᴾ[ G ]

  open hPropStructure NG.PS.𝒮ᴾ[ G ]
    using () renaming ( _≈ˢ_ to _≈ᴱ_; _∈ˢ_ to _∈ᴱ_ )

  checked : S → NG.PS.Nameᴾ
  checked = CopyBase.groundName

  checked-inductive : ⟨ CBᴱ.isInductive (checked w) ⟩
  checked-inductive = subst ⟨_⟩ (CBᴱ.IsInductive-bridge (checked w))
    (subst ⟨_⟩
      (sym (Copy.groundSat CBᴳ.IsInductiveφ Δ₀-IsInductiveφ (w ∷ [])))
      (subst ⟨_⟩ (sym (CBᴳ.IsInductive-bridge w)) (hw .fst)))

  checked-empty : (n : S) → ⟨ FVᴳ.emptyPred n ⟩
    → ⟨ FVᴱ.emptyPred (checked n) ⟩
  checked-empty n hn = subst ⟨_⟩ (FVᴱ.empty-reading zero (checked n ∷ []))
    (subst ⟨_⟩
      (sym (Copy.groundSat (FVᴳ.emptyAt zero) (FVᴳ.empty-bounded zero) (n ∷ [])))
      (subst ⟨_⟩ (sym (FVᴳ.empty-reading zero (n ∷ []))) hn))

  checked-successor : (n m : S) → ⟨ CBᴳ.isSuccOf n m ⟩
    → ⟨ CBᴱ.isSuccOf (checked n) (checked m) ⟩
  checked-successor n m h =
    subst ⟨_⟩ (CBᴱ.IsSuccOf-bridge (checked n) (checked m))
      (subst ⟨_⟩
        (sym (Copy.groundSat CBᴳ.IsSuccOfφ Δ₀-IsSuccOfφ (n ∷ m ∷ [])))
        (subst ⟨_⟩ (sym (CBᴳ.IsSuccOf-bridge n m)) h))

  empty-equal : (a b : NG.PS.Nameᴾ)
    → ⟨ FVᴱ.emptyPred a ⟩ → ⟨ FVᴱ.emptyPred b ⟩ → ⟨ a ≈ᴱ b ⟩
  empty-equal a b ha hb = NG.PS.P.Ext.extensional G a b (λ x →
    (λ h → Empty.rec* (ha x h)) , (λ h → Empty.rec* (hb x h)))

  successor-equal : (a b c : NG.PS.Nameᴾ)
    → ⟨ CBᴱ.isSuccOf a c ⟩ → ⟨ CBᴱ.isSuccOf b c ⟩ → ⟨ a ≈ᴱ b ⟩
  successor-equal a b c ha hb = NG.PS.P.Ext.extensional G a b (λ x →
    forward x , backward x)
    where
      forward : (x : NG.PS.Nameᴾ) → ⟨ x ∈ᴱ a ⟩ → ⟨ x ∈ᴱ b ⟩
      forward x hx = PT.rec (snd (x ∈ᴱ b)) choose (ha .snd .snd x hx)
        where
          choose : ⟨ x ∈ᴱ c ⟩ ⊎ ⟨ x ≈ᴱ c ⟩ → ⟨ x ∈ᴱ b ⟩
          choose (inl hxc) = hb .snd .fst x hxc
          choose (inr e) = E.∈-congˡ (E.≈-sym e) (hb .fst)

      backward : (x : NG.PS.Nameᴾ) → ⟨ x ∈ᴱ b ⟩ → ⟨ x ∈ᴱ a ⟩
      backward x hx = PT.rec (snd (x ∈ᴱ a)) choose (hb .snd .snd x hx)
        where
          choose : ⟨ x ∈ᴱ c ⟩ ⊎ ⟨ x ≈ᴱ c ⟩ → ⟨ x ∈ᴱ a ⟩
          choose (inl hxc) = ha .snd .fst x hxc
          choose (inr e) = E.∈-congˡ (E.≈-sym e) (ha .fst)

  checked-member-in-inductive : (n : S) → ⟨ n ∈ˢ w ⟩
    → (i : NG.PS.Nameᴾ) → ⟨ CBᴱ.isInductive i ⟩ → ⟨ checked n ∈ᴱ i ⟩
  checked-member-in-inductive =
    WFI.induction accessible
      {P = λ n → ⟨ n ∈ˢ w ⟩ → (i : NG.PS.Nameᴾ)
        → ⟨ CBᴱ.isInductive i ⟩ → ⟨ checked n ∈ᴱ i ⟩}
      step
    where
      step : (n : S)
        → ((m : S) → ⟨ m ∈ˢ n ⟩ → ⟨ m ∈ˢ w ⟩
          → (i : NG.PS.Nameᴾ) → ⟨ CBᴱ.isInductive i ⟩
          → ⟨ checked m ∈ᴱ i ⟩)
        → ⟨ n ∈ˢ w ⟩
        → (i : NG.PS.Nameᴾ) → ⟨ CBᴱ.isInductive i ⟩
        → ⟨ checked n ∈ᴱ i ⟩
      step n below hn i hi = PT.rec (snd (checked n ∈ᴱ i)) choose
        (OI.omega-predecessor w hw n hn)
        where
          choose : ⟨ FVᴳ.emptyPred n ⟩
            ⊎ ⟨ ⋁ S (λ m → (m ∈ˢ w) ⊓ CBᴳ.isSuccOf n m) ⟩
            → ⟨ checked n ∈ᴱ i ⟩
          choose (inl emptyN) = PT.rec (snd (checked n ∈ᴱ i)) atEmpty
            (hi .fst)
            where
              atEmpty : Σ[ e ∈ NG.PS.Nameᴾ ]
                (⟨ e ∈ᴱ i ⟩ × ⟨ FVᴱ.emptyPred e ⟩)
                → ⟨ checked n ∈ᴱ i ⟩
              atEmpty (e , hei , emptyE) = E.∈-congˡ
                (empty-equal e (checked n) emptyE (checked-empty n emptyN)) hei
          choose (inr successorN) = PT.rec (snd (checked n ∈ᴱ i)) atPredecessor
            successorN
            where
              atPredecessor : Σ[ m ∈ S ]
                (⟨ m ∈ˢ w ⟩ × ⟨ CBᴳ.isSuccOf n m ⟩)
                → ⟨ checked n ∈ᴱ i ⟩
              atPredecessor (m , hm , successorNM) =
                PT.rec (snd (checked n ∈ᴱ i)) atSuccessor
                  (hi .snd (checked m) (below m (successorNM .fst) hm i hi))
                where
                  atSuccessor : Σ[ s ∈ NG.PS.Nameᴾ ]
                    (⟨ s ∈ᴱ i ⟩ × ⟨ CBᴱ.isSuccOf s (checked m) ⟩)
                    → ⟨ checked n ∈ᴱ i ⟩
                  atSuccessor (s , hsi , successorS) = E.∈-congˡ
                    (successor-equal s (checked n) (checked m) successorS
                      (checked-successor n m successorNM)) hsi

  checked-minimal : (i : NG.PS.Nameᴾ) → ⟨ CBᴱ.isInductive i ⟩
    → (χ : NG.PS.Nameᴾ) → ⟨ χ ∈ᴱ checked w ⟩ → ⟨ χ ∈ᴱ i ⟩
  checked-minimal i hi χ hχ = PT.rec (snd (χ ∈ᴱ i)) atMember
    (subst ⟨_⟩ (Copy.check-value w (fst χ)) hχ)
    where
      atMember : Σ[ n ∈ S ]
        (⟨ n ∈ˢ w ⟩ × ⟨ χ ≈ᴱ checked n ⟩)
        → ⟨ χ ∈ᴱ i ⟩
      atMember (n , hn , e) = E.∈-congˡ (E.≈-sym e)
        (checked-member-in-inductive n hn i hi)

  checked-omega : ⟨ CBᴱ.isOmega (checked w) ⟩
  checked-omega = checked-inductive , checked-minimal

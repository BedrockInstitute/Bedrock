{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile
import Cubical.HITs.PropositionalTruncation as PT
import K4.Algebra
import K4.Implication
import K9.BooleanNameGround
import K9.BooleanAtomic
import K10.CohenBooleanCands
import K10.CohenBooleanSubset
import K10.CohenBooleanPower
import K10.CohenBooleanPowerMem

module K10.CohenBooleanPowerWeight
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (families : NameKernel.Families 𝒮)
  (accessible : NameKernel.Accessibility 𝒮)
  (images : NameKernel.MemberImage 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (κ w : ZFStructure.S 𝒮)
  (lem : LEM ℓ)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open PT using ( ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

module Mem = K10.CohenBooleanPowerMem 𝒮 families accessible images pow κ w lem
module Cands = Mem.Cands
module Sub = Mem.Sub
module Power = Mem.Power
module BNG = Mem.BNG
open BNG using ( B ; weight ; weight-upper ; weight-least ; module BK
               ; module IC ; module BSupport ; module Translation ; module NG )
open NG using ( extensional ; ≈ˢ-paths )
open K4.Algebra 𝒮 using ( Pt ; _≤ᴮ_ ; ⊆ˢ-trans ; ≤ᴮ-refl ; Pt≡ )
open K4.Algebra.Lattice IC.codedLattice
  using ( _⊓ᴮ_ ; ⊤ᴮ ; ⊓-lb₁ ; ⊓-lb₂ ; ⊓-glb )
open K4.Implication 𝒮 extensional ≈ˢ-paths B IC.codedLattice IC.codedComplement
  using ( ≤ᴮ-antisym ; ⊤-greatest )
module BAT = K9.BooleanAtomic.Atomic 𝒮 families accessible images pow κ w lem
  using ( _∈ᴮ_ ; _≈ᴮ_ ; ∈ᴮ-ub ; ∈ᴮ-lub )

≈→≡ : {a b : S} → ⟨ a ≈ˢ b ⟩ → a ≡ b
≈→≡ {a} {b} = subst ⟨_⟩ (≈ˢ-paths a b)

weight-ge : (σ : S) → ⟨ σ ∈ˢ Cands.cands ⟩
  → ⟨ Sub.subsetVal (Translation.trᴮ σ) ≤ᴮ weight Power.powerB (Translation.trᴮ σ) ⟩
weight-ge σ hσ = subst
  (λ b → ⟨ b ≤ᴮ weight Power.powerB (Translation.trᴮ σ) ⟩)
  (sym (Sub.candWeight-pt σ))
  (weight-upper Power.powerB (Translation.trᴮ σ)
    (Sub.candWeight σ , Sub.candWeight-inB σ) (Mem.entry-in-power σ hσ))

entry-from-power : (x : S) (b : Pt B)
  → ⟨ BK.entry x (fst b) ∈ˢ Power.powerB ⟩
  → PT.∥ (Σ[ σ ∈ S ] (⟨ σ ∈ˢ Cands.cands ⟩
      × ((x ≡ Translation.trᴮ σ) × (fst b ≡ Sub.candWeight σ)))) ∥₁
entry-from-power x b he = PT.rec PT.squash₁ from-spec
  (subst ⟨_⟩ (Power.powerB-spec (BK.entry x (fst b))) he)
  where
  from-spec : Σ[ σ ∈ S ] ⟨ ⋁ ⟨ σ ∈ˢ Cands.cands ⟩
                (λ _ → BK.entry x (fst b) ≈ˢ Sub.candEntry σ) ⟩
    → PT.∥ (Σ[ σ ∈ S ] (⟨ σ ∈ˢ Cands.cands ⟩
        × ((x ≡ Translation.trᴮ σ) × (fst b ≡ Sub.candWeight σ)))) ∥₁
  from-spec (σ , inner) = PT.map from-eq inner
    where
    from-eq : ⟨ σ ∈ˢ Cands.cands ⟩ × ⟨ BK.entry x (fst b) ≈ˢ Sub.candEntry σ ⟩
      → Σ[ σ ∈ S ] (⟨ σ ∈ˢ Cands.cands ⟩
          × ((x ≡ Translation.trᴮ σ) × (fst b ≡ Sub.candWeight σ)))
    from-eq (hσ , heq) =
      σ , hσ
      , ( fst (BK.entry-inj (≈→≡ heq ∙ Sub.candEntry-weight σ))
        , snd (BK.entry-inj (≈→≡ heq ∙ Sub.candEntry-weight σ)) )

weight-le : (σ : S) → ⟨ σ ∈ˢ Cands.cands ⟩
  → ⟨ weight Power.powerB (Translation.trᴮ σ)
      ≤ᴮ Sub.subsetVal (Translation.trᴮ σ) ⟩
weight-le σ hσ = weight-least Power.powerB (Translation.trᴮ σ)
  (Sub.subsetVal (Translation.trᴮ σ)) λ b he →
    PT.rec (snd (b ≤ᴮ Sub.subsetVal (Translation.trᴮ σ)))
      (from-entry b he) (entry-from-power (Translation.trᴮ σ) b he)
  where
  from-entry : (b : Pt B)
    → ⟨ BK.entry (Translation.trᴮ σ) (fst b) ∈ˢ Power.powerB ⟩
    → Σ[ τ ∈ S ] (⟨ τ ∈ˢ Cands.cands ⟩
        × ((Translation.trᴮ σ ≡ Translation.trᴮ τ)
          × (fst b ≡ Sub.candWeight τ)))
    → ⟨ b ≤ᴮ Sub.subsetVal (Translation.trᴮ σ) ⟩
  from-entry b he (τ , hτ , xpath , bpath) =
    subst (λ z → ⟨ b ≤ᴮ z ⟩)
      (Pt≡ {B} {b} {Sub.candWeight τ , Sub.candWeight-inB τ} bpath
        ∙ sym (Sub.candWeight-pt τ)
        ∙ cong Sub.subsetVal (sym xpath))
      (≤ᴮ-refl b)

opaque
  weight-eq : (σ : S) → ⟨ σ ∈ˢ Cands.cands ⟩
    → weight Power.powerB (Translation.trᴮ σ)
      ≡ Sub.subsetVal (Translation.trᴮ σ)
  weight-eq σ hσ = ≤ᴮ-antisym (weight-le σ hσ) (weight-ge σ hσ)

member-lub : (τ : S) (c : Pt B)
  → ((σ : S) → ⟨ σ ∈ˢ Cands.cands ⟩
      → ⟨ (Sub.subsetVal (Translation.trᴮ σ)
            ⊓ᴮ BAT._≈ᴮ_ τ (Translation.trᴮ σ)) ≤ᴮ c ⟩)
  → ⟨ BAT._∈ᴮ_ τ Power.powerB ≤ᴮ c ⟩
member-lub τ c hyp = BAT.∈ᴮ-lub τ Power.powerB c λ x hx →
  PT.rec (snd ((weight Power.powerB x ⊓ᴮ BAT._≈ᴮ_ τ x) ≤ᴮ c))
    (from-support x hx) (BSupport.entry-out Power.powerB x hx)
  where
  from-support : (x : S) → ⟨ x ∈ˢ BSupport.support Power.powerB ⟩
    → Σ[ b ∈ S ] (⟨ b ∈ˢ B ⟩ × ⟨ BK.entry x b ∈ˢ Power.powerB ⟩)
    → ⟨ (weight Power.powerB x ⊓ᴮ BAT._≈ᴮ_ τ x) ≤ᴮ c ⟩
  from-support x hx (b , hb , he) = PT.rec
    (snd ((weight Power.powerB x ⊓ᴮ BAT._≈ᴮ_ τ x) ≤ᴮ c))
    (from-cand x b hb he) (entry-from-power x (b , hb) he)
    where
    from-cand : (x b : S) (hb : ⟨ b ∈ˢ B ⟩)
      → ⟨ BK.entry x b ∈ˢ Power.powerB ⟩
      → Σ[ σ ∈ S ] (⟨ σ ∈ˢ Cands.cands ⟩
          × ((x ≡ Translation.trᴮ σ) × (b ≡ Sub.candWeight σ)))
      → ⟨ (weight Power.powerB x ⊓ᴮ BAT._≈ᴮ_ τ x) ≤ᴮ c ⟩
    from-cand x b hb he (σ , hσ , xpath , bpath) =
      subst (λ z → ⟨ (z ⊓ᴮ BAT._≈ᴮ_ τ x) ≤ᴮ c ⟩)
        (sym (cong (weight Power.powerB) xpath ∙ weight-eq σ hσ))
        (subst (λ y → ⟨ (Sub.subsetVal (Translation.trᴮ σ)
                          ⊓ᴮ BAT._≈ᴮ_ τ y) ≤ᴮ c ⟩) (sym xpath)
          (hyp σ hσ))

{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile

module K10.BooleanPairs
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (families : NameKernel.Families 𝒮)
  (accessible : NameKernel.Accessibility 𝒮)
  (images : NameKernel.MemberImage 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (κ w : ZFStructure.S 𝒮)
  (lem : LEM ℓ)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.HITs.PropositionalTruncation as PT
import GroundDescription
import K4.Algebra
import K4.Implication
import K5.Frame
import K9.BooleanNameGround
import K9.BooleanSeparation
import K9.PairNames

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open PT using ( ∥_∥₁; ∣_∣₁ )
module BG = K9.BooleanNameGround 𝒮 families accessible images pow κ w lem
  using ( B; weight; weight-upper; entry-agrees; module NG; module IC; module BK
        ; module Atomic; module Laws; module Translation; module BSupport; module Base )
module Pair = K9.PairNames 𝒮 families accessible images pow κ w
  using ( singleCode; single-spec; pairCode; pair-spec; pairNm; orderedNm; singleNm; layer )
open BG.NG using ( extensional; ≈ˢ-paths )
module GD = GroundDescription 𝒮 extensional ≈ˢ-paths using ( ext-path )
open K4.Algebra 𝒮 using ( Pt; _≤ᴮ_; ≤ᴮ-refl; ⊆ˢ-trans )
open K4.Algebra.Lattice BG.IC.codedLattice
open K4.Implication 𝒮 extensional ≈ˢ-paths BG.B BG.IC.codedLattice BG.IC.codedComplement
  using ( ≤ᴮ-antisym; ⊓-⊤; ⊓-comm )
open BG.Atomic using () renaming ( _≈ᴮ_ to eq; _∈ᴮ_ to mem )
module FP = K5.Frame.Poset 𝒮 BG.NG.C.carrier BG.NG.C.order
module FF = FP.Forcing extensional ≈ˢ-paths BG.B BG.IC.codedLattice BG.IC.codedComplement BG.IC.codedComplete
  (BG.Base.codedBase lem) using ( ⊩ᴮ-intro )
open FP using ( Cond )
open K5.Frame.Poset.ForcingBase (BG.Base.codedBase lem) using ( i; inhabited )
module Separation = K9.BooleanSeparation 𝒮 extensional ≈ˢ-paths
  BG.NG.C.carrier BG.NG.C.order BG.B BG.IC.codedLattice BG.IC.codedComplement BG.IC.codedComplete
  (BG.Base.codedBase lem) using ( all-force-top )

private
  ≈→≡ : {a b : S} → ⟨ a ≈ˢ b ⟩ → a ≡ b
  ≈→≡ {a} {b} = subst ⟨_⟩ (≈ˢ-paths a b)

  ≈-refl : (a : S) → ⟨ a ≈ˢ a ⟩
  ≈-refl a = subst ⟨_⟩ (sym (≈ˢ-paths a a)) refl

tr : S → S
tr = BG.Translation.trᴮ

singleB : S → S
singleB m = tr (Pair.singleCode m)

pairB : S → S → S
pairB m n = tr (Pair.pairCode m n)

orderedB : S → S → S
orderedB m n = pairB (Pair.singleCode m) (Pair.pairCode m n)

pairB-name : (σ τ : BG.NG.K.Name) → ⟨ BG.BK.IsName (pairB (fst σ) (fst τ)) ⟩
pairB-name σ τ = BG.Translation.trᴮ-name (fst (Pair.pairNm σ τ)) (snd (Pair.pairNm σ τ))

singleB-name : (σ : BG.NG.K.Name) → ⟨ BG.BK.IsName (singleB (fst σ)) ⟩
singleB-name σ = BG.Translation.trᴮ-name (fst (Pair.singleNm σ)) (snd (Pair.singleNm σ))

orderedB-name : (σ τ : BG.NG.K.Name) → ⟨ BG.BK.IsName (orderedB (fst σ) (fst τ)) ⟩
orderedB-name σ τ = BG.Translation.trᴮ-name (fst (Pair.orderedNm σ τ)) (snd (Pair.orderedNm σ τ))

pairB-entry : (m n x : S) → (x ≡ m) ⊎ (x ≡ n) → (p : Cond)
  → ⟨ BG.BK.entry (tr x) (fst (i p)) ∈ˢ pairB m n ⟩
pairB-entry m n x choice p = subst ⟨_⟩ (sym (BG.Translation.trᴮ-entries (Pair.pairCode m n) _))
  ∣ x , ∣ fst p , ∣ snd p , source , ≈-refl (BG.BK.entry (tr x) (fst (i p))) ∣₁ ∣₁ ∣₁
  where
  source : ⟨ BG.BK.entry x (fst p) ∈ˢ Pair.pairCode m n ⟩
  source = subst (λ e → ⟨ e ∈ˢ Pair.pairCode m n ⟩) (sym (BG.entry-agrees x (fst p)))
    (subst ⟨_⟩ (sym (Pair.pair-spec m n (BG.NG.K.entry x (fst p)))) (choose choice))
    where
    choose : (x ≡ m) ⊎ (x ≡ n)
      → ⟨ Pair.layer m (BG.NG.K.entry x (fst p)) ⊔ Pair.layer n (BG.NG.K.entry x (fst p)) ⟩
    choose (inl path) = ∣ inl ∣ fst p , snd p ,
      subst (λ y → ⟨ BG.NG.K.entry x (fst p) ≈ˢ BG.NG.K.entry y (fst p) ⟩)
        path (≈-refl (BG.NG.K.entry x (fst p))) ∣₁ ∣₁
    choose (inr path) = ∣ inr ∣ fst p , snd p ,
      subst (λ y → ⟨ BG.NG.K.entry x (fst p) ≈ˢ BG.NG.K.entry y (fst p) ⟩)
        path (≈-refl (BG.NG.K.entry x (fst p))) ∣₁ ∣₁

pairB-entry-out : (m n x : S) (b : Pt BG.B)
  → ⟨ BG.BK.entry x (fst b) ∈ˢ pairB m n ⟩
  → ∥ (x ≡ tr m) ⊎ (x ≡ tr n) ∥₁
pairB-entry-out m n x b he = PT.rec PT.squash₁
  (λ { (z , rest) → PT.rec PT.squash₁
    (λ { (p , rest') → PT.rec PT.squash₁
      (λ { (hp , source , path) → translated z p hp source path }) rest' }) rest })
  (subst ⟨_⟩ (BG.Translation.trᴮ-entries (Pair.pairCode m n) _) he)
  where
  translated : (z p : S) (hp : ⟨ p ∈ˢ BG.NG.C.carrier ⟩)
    → ⟨ BG.BK.entry z p ∈ˢ Pair.pairCode m n ⟩
    → ⟨ BG.BK.entry x (fst b) ≈ˢ BG.BK.entry (tr z) (fst (i (p , hp))) ⟩
    → ∥ (x ≡ tr m) ⊎ (x ≡ tr n) ∥₁
  translated z p hp source path = PT.rec PT.squash₁ decide
    (subst ⟨_⟩ (Pair.pair-spec m n (BG.NG.K.entry z p))
      (subst (λ e → ⟨ e ∈ˢ Pair.pairCode m n ⟩) (BG.entry-agrees z p) source))
    where
    from-layer : (y : S) → ⟨ Pair.layer y (BG.NG.K.entry z p) ⟩ → ∥ x ≡ tr y ∥₁
    from-layer y = PT.map (λ { (q , hq , sourcepath) →
      fst (BG.BK.entry-inj (≈→≡ path)) ∙ cong tr (fst (BG.NG.K.entry-inj (≈→≡ sourcepath))) })

    decide : ⟨ Pair.layer m (BG.NG.K.entry z p) ⟩ ⊎ ⟨ Pair.layer n (BG.NG.K.entry z p) ⟩
      → ∥ (x ≡ tr m) ⊎ (x ≡ tr n) ∥₁
    decide (inl hm) = PT.map inl (from-layer m hm)
    decide (inr hn) = PT.map inr (from-layer n hn)

pairB-support-out : (m n x : S) → ⟨ x ∈ˢ BG.BSupport.support (pairB m n) ⟩
  → ∥ (x ≡ tr m) ⊎ (x ≡ tr n) ∥₁
pairB-support-out m n x hx = PT.rec PT.squash₁
  (λ { (b , hb , he) → pairB-entry-out m n x (b , hb) he })
  (BG.BSupport.entry-out (pairB m n) x hx)

pairB-support-in : (m n x : S) → (x ≡ m) ⊎ (x ≡ n)
  → ⟨ tr x ∈ˢ BG.BSupport.support (pairB m n) ⟩
pairB-support-in m n x choice = PT.rec (snd (tr x ∈ˢ BG.BSupport.support (pairB m n)))
  (λ p → BG.BSupport.entry-in (pairB m n) (tr x) (fst (i p)) (snd (i p))
    (pairB-entry m n x choice p)) inhabited

pairB-weight : (m n x : S) → (x ≡ m) ⊎ (x ≡ n)
  → BG.weight (pairB m n) (tr x) ≡ ⊤ᴮ
pairB-weight m n x choice = Separation.all-force-top lem (BG.weight (pairB m n) (tr x))
  (λ p → FF.⊩ᴮ-intro p _ (BG.weight-upper (pairB m n) (tr x) (i p) (pairB-entry m n x choice p)))

pairB-member-upper : (m n x z : S) → (x ≡ m) ⊎ (x ≡ n)
  → ⟨ eq z (tr x) ≤ᴮ mem z (pairB m n) ⟩
pairB-member-upper m n x z choice = subst (λ v → ⟨ v ≤ᴮ mem z (pairB m n) ⟩)
  (cong (λ b → b ⊓ᴮ eq z (tr x)) (pairB-weight m n x choice)
    ∙ ⊓-comm ⊤ᴮ (eq z (tr x)) ∙ ⊓-⊤ (eq z (tr x)))
  (BG.Atomic.∈ᴮ-ub z (pairB m n) (tr x) (pairB-support-in m n x choice))

pairB-member-least : (m n z : S) (v : Pt BG.B)
  → ⟨ eq z (tr m) ≤ᴮ v ⟩ → ⟨ eq z (tr n) ≤ᴮ v ⟩
  → ⟨ mem z (pairB m n) ≤ᴮ v ⟩
pairB-member-least m n z v left right = BG.Atomic.∈ᴮ-lub z (pairB m n) v
  (λ x hx → PT.rec (snd ((BG.weight (pairB m n) x ⊓ᴮ eq z x) ≤ᴮ v))
    (λ { (inl path) → ⊆ˢ-trans (⊓-lb₂ (BG.weight (pairB m n) x) (eq z x))
          (subst (λ y → ⟨ eq z y ≤ᴮ v ⟩) (sym path) left)
       ; (inr path) → ⊆ˢ-trans (⊓-lb₂ (BG.weight (pairB m n) x) (eq z x))
          (subst (λ y → ⟨ eq z y ≤ᴮ v ⟩) (sym path) right) })
    (pairB-support-out m n x hx))

pairB-member-value : (m n z : S)
  → mem z (pairB m n) ≡ (eq z (tr m) ⊔ᴮ eq z (tr n))
pairB-member-value m n z = ≤ᴮ-antisym
  (pairB-member-least m n z (eq z (tr m) ⊔ᴮ eq z (tr n))
    (⊔-ub₁ (eq z (tr m)) (eq z (tr n))) (⊔-ub₂ (eq z (tr m)) (eq z (tr n))))
  (⊔-lub (eq z (tr m)) (eq z (tr n)) (mem z (pairB m n))
    (pairB-member-upper m n m z (inl refl)) (pairB-member-upper m n n z (inr refl)))

private
  duplicate : (P : Ω) → (P ⊔ P) ≡ P
  duplicate P = ⇔toPath (PT.rec (snd P) (λ { (inl h) → h; (inr h) → h }))
    (λ h → ∣ inl h ∣₁)

  pair-diagonal : (m : S) → Pair.pairCode m m ≡ Pair.singleCode m
  pair-diagonal m = GD.ext-path (λ e → Pair.pair-spec m m e
    ∙ duplicate (Pair.layer m e) ∙ sym (Pair.single-spec m e))

  join-diagonal : (b : Pt BG.B) → (b ⊔ᴮ b) ≡ b
  join-diagonal b = ≤ᴮ-antisym (⊔-lub b b b (≤ᴮ-refl b) (≤ᴮ-refl b)) (⊔-ub₁ b b)

singleB-member-value : (m z : S) → mem z (singleB m) ≡ eq z (tr m)
singleB-member-value m z = cong (λ n → mem z (tr n)) (sym (pair-diagonal m))
  ∙ pairB-member-value m m z ∙ join-diagonal (eq z (tr m))

orderedB-member-value : (m n z : S)
  → mem z (orderedB m n) ≡ (eq z (singleB m) ⊔ᴮ eq z (pairB m n))
orderedB-member-value m n z = pairB-member-value (Pair.singleCode m) (Pair.pairCode m n) z

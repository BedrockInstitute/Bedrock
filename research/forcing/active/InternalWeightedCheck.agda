{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile
import NameKernel

module InternalWeightedCheck
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (families : NameKernel.Families 𝒮)
  (accessible : NameKernel.Accessibility 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (W : ZFStructure.S 𝒮)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import Cubical.Induction.WellFounded using ( Acc; acc )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )
import GroundDescription
import K8.GroundSets
import WeightedCheckRecursion

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open NameKernel.Families families using ( sets; hasCollect )
open NameKernel.Sets sets using ( core; hasUnion; hasSeparation )
open NameKernel.Core core using ( extensional; hasPair; ≈ˢ-paths )

module K = NameKernel.Kernel 𝒮 core accessible W
  using ( entry; entry-inj; entry-isKPair; IsName; Name; Shape; Child; name-intro )
module GS = K8.GroundSets.Ground 𝒮 extensional ≈ˢ-paths hasPair hasUnion pow hasSeparation W
  using ( ordered; ordered-unique; ≈→≡; product; product-in; product-out; singleton; singleton-witness )
module C = WeightedCheckRecursion.Construct 𝒮 extensional ≈ˢ-paths accessible W
  hasPair hasUnion pow hasSeparation hasCollect W
  using ( chk; chk-spec; check-graph; table; table-mem; table-only; diagonal-image )
module GD = GroundDescription 𝒮 extensional ≈ˢ-paths using ( ext-path )

entry-agrees : (x b : S) → GS.ordered x b ≡ K.entry x b
entry-agrees x b = sym (GS.ordered-unique (K.entry x b) x b (K.entry-isKPair x b))

chk : S → S
chk = C.chk

chk-spec : (a z : S) → (z ∈ˢ chk a) ≡
  ⋁ S (λ u → (u ∈ˢ a) ⊓ ⋁ S (λ p → (p ∈ˢ W) ⊓ (z ≈ˢ K.entry (chk u) p)))
chk-spec a z = C.chk-spec a z ∙ cong (⋁ S) (funExt λ u →
  cong ((u ∈ˢ a) ⊓_) (cong (⋁ S) (funExt λ p →
    cong ((p ∈ˢ W) ⊓_) (cong (z ≈ˢ_) (entry-agrees (chk u) p)))))

entry-out : (a x b : S) → ⟨ K.entry x b ∈ˢ chk a ⟩
  → ⟨ ⋁ S (λ u → (u ∈ˢ a) ⊓ ((x ≡ chk u) , isSetS x (chk u))) ⟩
entry-out a x b h = PT.rec PT.squash₁ (λ { (u , hu , weights) →
  PT.map (λ { (p , hp , eq) → u , hu , K.entry-inj (GS.≈→≡ eq) .fst }) weights })
  (subst ⟨_⟩ (chk-spec a (K.entry x b)) h)

valid-acc : (a : S) → Acc _∈ᵗ_ a → ⟨ K.IsName (chk a) ⟩
valid-acc a (acc below) = K.name-intro (chk a) shape hereditary
  where
  shape : ⟨ K.Shape (chk a) ⟩
  shape e he = PT.rec PT.squash₁ (λ { (u , hu , weights) →
    PT.map (λ { (p , hp , eq) → chk u , p , GS.≈→≡ eq , hp }) weights })
    (subst ⟨_⟩ (chk-spec a e) he)

  hereditary : (x : S) → K.Child x (chk a) → ⟨ K.IsName x ⟩
  hereditary x = PT.rec (snd (K.IsName x)) λ { (b , hb) →
    PT.rec (snd (K.IsName x))
      (λ { (u , hu , eq) → subst (λ j → ⟨ K.IsName j ⟩) (sym eq)
        (valid-acc u (below u hu)) }) (entry-out a x b hb) }

chk-name : (a : S) → ⟨ K.IsName (chk a) ⟩
chk-name a = valid-acc a (accessible a)

check : S → K.Name
check a = chk a , chk-name a

import NameImage
module NI = NameImage 𝒮 extensional ≈ˢ-paths using ( InternalImage )

genericName : S
genericName = NI.InternalImage.img C.diagonal-image W

generic-spec : (e : S) → (e ∈ˢ genericName) ≡
  ⋁ S (λ p → (p ∈ˢ W) ⊓ (e ≈ˢ K.entry (chk p) p))
generic-spec e = NI.InternalImage.img-spec C.diagonal-image W e ∙
  cong (⋁ S) (funExt λ p → cong ((p ∈ˢ W) ⊓_)
    (cong (e ≈ˢ_) (entry-agrees (chk p) p)))

spread : S → S
spread x = GS.product (GS.singleton x) W

spread-spec : (x e : S) → (e ∈ˢ spread x) ≡
  ⋁ S (λ p → (p ∈ˢ W) ⊓ (e ≈ˢ K.entry x p))
spread-spec x e = ⇔toPath forward backward
  where
  forward : ⟨ e ∈ˢ spread x ⟩ → ⟨ ⋁ S (λ p → (p ∈ˢ W) ⊓ (e ≈ˢ K.entry x p)) ⟩
  forward h = PT.map (λ { (t , p , ht , hp , kp) → p , hp ,
    subst ⟨_⟩ (sym (≈ˢ-paths e (K.entry x p)))
      (GS.ordered-unique e t p kp ∙
        cong (λ j → GS.ordered j p) (GS.≈→≡ (GS.singleton-witness x .snd t ht)) ∙
        entry-agrees x p) }) (GS.product-out (GS.singleton x) W e h)

  backward : ⟨ ⋁ S (λ p → (p ∈ˢ W) ⊓ (e ≈ˢ K.entry x p)) ⟩ → ⟨ e ∈ˢ spread x ⟩
  backward = PT.rec (snd (e ∈ˢ spread x)) λ { (p , hp , eq) →
    subst (λ j → ⟨ j ∈ˢ spread x ⟩)
      (entry-agrees x p ∙ sym (GS.≈→≡ eq))
      (GS.product-in (GS.singleton x) W x p (GS.singleton-witness x .fst) hp) }

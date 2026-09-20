{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile
import NameKernel

module InternalCheck
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (families : NameKernel.Families 𝒮)
  (accessible : NameKernel.Accessibility 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (W w : ZFStructure.S 𝒮)
  (hw : ⟨ ZFStructure._∈ˢ_ 𝒮 w W ⟩)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import Cubical.Induction.WellFounded using ( Acc; acc )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )
import GroundDescription
import K8.GroundSets
import CheckRecursion

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open NameKernel.Families families using ( sets; hasCollect )
open NameKernel.Sets sets using ( core; hasUnion; hasSeparation )
open NameKernel.Core core using ( extensional; hasPair; ≈ˢ-paths )

module K = NameKernel.Kernel 𝒮 core accessible W
  using ( entry; entry-inj; entry-isKPair; IsName; Name; Shape; Child; name-intro )
module GS = K8.GroundSets.Ground 𝒮 extensional ≈ˢ-paths hasPair hasUnion pow hasSeparation W
  using ( ordered; ordered-unique; ≈→≡ )
module C = CheckRecursion.Construct 𝒮 extensional ≈ˢ-paths accessible w
  hasPair hasUnion pow hasSeparation hasCollect W
  using ( chk; chk-spec; check-graph; check-internal; table; table-mem; table-only )
module GD = GroundDescription 𝒮 extensional ≈ˢ-paths using ( ext-path )

entry-agrees : (x b : S) → GS.ordered x b ≡ K.entry x b
entry-agrees x b = sym (GS.ordered-unique (K.entry x b) x b (K.entry-isKPair x b))

entry-in : (a u : S) → ⟨ u ∈ˢ a ⟩ → ⟨ K.entry (C.chk u) w ∈ˢ C.chk a ⟩
entry-in a u hu = subst ⟨_⟩ (sym (C.chk-spec a (K.entry (C.chk u) w)))
  ∣ u , hu , subst ⟨_⟩ (sym (≈ˢ-paths (K.entry (C.chk u) w) (GS.ordered (C.chk u) w)))
    (sym (entry-agrees (C.chk u) w)) ∣₁

entry-out : (a x b : S) → ⟨ K.entry x b ∈ˢ C.chk a ⟩
  → ⟨ ⋁ S (λ u → (u ∈ˢ a) ⊓ ((x ≡ C.chk u) , isSetS x (C.chk u))) ⟩
entry-out a x b h = PT.map (λ { (u , hu , eq) → u , hu ,
  K.entry-inj (GS.≈→≡ eq ∙ entry-agrees (C.chk u) w) .fst })
  (subst ⟨_⟩ (C.chk-spec a (K.entry x b)) h)

valid-acc : (a : S) → Acc _∈ᵗ_ a → ⟨ K.IsName (C.chk a) ⟩
valid-acc a (acc below) = K.name-intro (C.chk a) shape hereditary
  where
  shape : ⟨ K.Shape (C.chk a) ⟩
  shape e he = PT.map (λ { (u , hu , eq) → C.chk u , w ,
    GS.≈→≡ eq ∙ entry-agrees (C.chk u) w , hw })
    (subst ⟨_⟩ (C.chk-spec a e) he)

  hereditary : (x : S) → K.Child x (C.chk a) → ⟨ K.IsName x ⟩
  hereditary x = PT.rec (snd (K.IsName x)) λ { (b , hb) →
    PT.rec (snd (K.IsName x))
      (λ { (u , hu , eq) → subst (λ j → ⟨ K.IsName j ⟩) (sym eq)
        (valid-acc u (below u hu)) }) (entry-out a x b hb) }

check-name : (a : S) → ⟨ K.IsName (C.chk a) ⟩
check-name a = valid-acc a (accessible a)

check : S → K.Name
check a = C.chk a , check-name a

injective-acc : (a : S) → Acc _∈ᵗ_ a → (b : S) → C.chk a ≡ C.chk b → a ≡ b
injective-acc a (acc below) b eq = GD.ext-path λ z → ⇔toPath (forward z) (backward z)
  where
  forward : (z : S) → ⟨ z ∈ˢ a ⟩ → ⟨ z ∈ˢ b ⟩
  forward z hz = PT.rec (snd (z ∈ˢ b))
    (λ { (u , hu , zu) → subst (λ j → ⟨ j ∈ˢ b ⟩)
      (sym (injective-acc z (below z hz) u zu)) hu })
    (entry-out b (C.chk z) w (subst (λ j → ⟨ K.entry (C.chk z) w ∈ˢ j ⟩) eq (entry-in a z hz)))

  backward : (z : S) → ⟨ z ∈ˢ b ⟩ → ⟨ z ∈ˢ a ⟩
  backward z hz = PT.rec (snd (z ∈ˢ a))
    (λ { (u , hu , zu) → subst (λ j → ⟨ j ∈ˢ a ⟩)
      (injective-acc u (below u hu) z (sym zu)) hu })
    (entry-out a (C.chk z) w (subst (λ j → ⟨ K.entry (C.chk z) w ∈ˢ j ⟩) (sym eq) (entry-in b z hz)))

check-injective : (a b : S) → check a ≡ check b → a ≡ b
check-injective a b eq = injective-acc a (accessible a) b (cong fst eq)

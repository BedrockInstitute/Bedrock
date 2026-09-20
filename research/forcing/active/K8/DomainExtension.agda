{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile

module K8.DomainExtension
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
    → ZFStructure._≈ˢ_ 𝒮 x y ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  (pair : OrdinaryProfile.Pairing 𝒮)
  (un : OrdinaryProfile.Union 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (sep : OrdinaryProfile.Separation 𝒮)
  (seed X Y : ZFStructure.S 𝒮)
  where

open import FOL.ZFStructure using ( module hPropStructure )

open import K8.FiniteVocabulary 𝒮 using ( adjoinPred )
import K8.GroundSets
import K8.FiniteOperations
import K8.PartialMaps
import K8.MapOperations
import K8.DomainFinite

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

module GS = K8.GroundSets.Ground 𝒮 ext paths pair un pow sep seed
module FO = K8.FiniteOperations 𝒮 ext paths pair un pow sep seed
module PM = K8.PartialMaps.Maps 𝒮 ext paths pair un pow sep seed X Y
module MO = K8.MapOperations.Operations 𝒮 ext paths pair un pow sep seed X Y
module DF = K8.DomainFinite 𝒮 ext paths pair un pow sep seed X Y

insert-adjoin : (p x y : S) → ⟨ adjoinPred (MO.insert p x y) p (GS.ordered x y) ⟩
insert-adjoin p x y = subst (λ b → ⟨ adjoinPred b p (GS.ordered x y) ⟩)
  (sym (cong (GS.join p) (MO.point-eq x y))) (FO.insert-witness p (GS.ordered x y))

domain-insert : (p x y : S) → ⟨ x ∈ˢ X ⟩ → ⟨ y ∈ˢ Y ⟩
  → ⟨ adjoinPred (PM.domain (MO.insert p x y)) (PM.domain p) x ⟩
domain-insert p x y hx hy = DF.domain-adjoin (MO.insert p x y) p (GS.ordered x y) x y
  (insert-adjoin p x y) hx hy (GS.ordered-witness x y)


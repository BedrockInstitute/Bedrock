{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile

module K8.Cohen
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
    → ZFStructure._≈ˢ_ 𝒮 x y ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  (pair : OrdinaryProfile.Pairing 𝒮)
  (un : OrdinaryProfile.Union 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (sep : OrdinaryProfile.Separation 𝒮)
  (κ w : ZFStructure.S 𝒮)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import Base.Classical using ( LEM )
open import CodedVocabulary 𝒮 using ( compatibleΔ; denseΔ )
import K8.GroundSets
import K8.PartialMaps
import K8.Presentation
import K8.MapOperations
import K8.CoordinateDense
import Cubical.Data.Empty as Empty

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

module GS = K8.GroundSets.Ground 𝒮 ext paths pair un pow sep κ

bit₀ : S
bit₀ = GS.empty

bit₁ : S
bit₁ = GS.singleton bit₀

two : S
two = GS.pairOf bit₀ bit₁

bit₀-in : ⟨ bit₀ ∈ˢ two ⟩
bit₀-in = GS.pairOf-inˡ bit₀ bit₁

bit₁-in : ⟨ bit₁ ∈ˢ two ⟩
bit₁-in = GS.pairOf-inʳ bit₀ bit₁

bits-distinct : ⟨ bit₀ ≈ˢ bit₁ ⟩ → ⟨ ⊥ ⟩
bits-distinct eq = GS.empty-out bit₀
  (subst (λ z → ⟨ bit₀ ∈ˢ z ⟩) (sym (GS.≈→≡ eq))
    (fst (GS.singleton-witness bit₀)))

coordinates : S
coordinates = GS.product κ w

module PM = K8.PartialMaps.Maps 𝒮 ext paths pair un pow sep κ coordinates two
module PC = K8.Presentation.CohenPresentation 𝒮 ext paths pair un pow sep κ coordinates two
module MO = K8.MapOperations.Operations 𝒮 ext paths pair un pow sep κ coordinates two
module CD = K8.CoordinateDense 𝒮 ext paths pair un pow sep κ coordinates two

open PC public using ( carrier; order; presentation; laws )

coordinate : S → S → S
coordinate = GS.ordered

coordinate-in : (α n : S) → ⟨ α ∈ˢ κ ⟩ → ⟨ n ∈ˢ w ⟩
  → ⟨ coordinate α n ∈ˢ coordinates ⟩
coordinate-in α n = GS.product-in κ w α n

D : S → S → S
D α n = CD.D (coordinate α n)

D-dense : LEM ℓ → (α n : S) → ⟨ α ∈ˢ κ ⟩ → ⟨ n ∈ˢ w ⟩
  → ⟨ denseΔ carrier order (D α n) ⟩
D-dense lem α n hα hn = CD.coordinate-dense lem (coordinate α n) bit₀
  (coordinate-in α n hα hn) bit₀-in

incompatible-bits : (α n : S) → ⟨ α ∈ˢ κ ⟩ → ⟨ n ∈ˢ w ⟩
  → ⟨ compatibleΔ carrier order
      (MO.point (coordinate α n) bit₀) (MO.point (coordinate α n) bit₁) ⟩
  → ⟨ ⊥ ⟩
incompatible-bits α n hα hn compat = bits-distinct
  (MO.compatible→agrees (MO.point x bit₀) (MO.point x bit₁)
    (MO.point-in-carrier x bit₀ hx bit₀-in)
    (MO.point-in-carrier x bit₁ hx bit₁-in) compat
    x hx bit₀ bit₀-in bit₁ bit₁-in
    (MO.point-refines x bit₀ , MO.point-refines x bit₁))
  where
  x : S
  x = coordinate α n
  hx : ⟨ x ∈ˢ coordinates ⟩
  hx = coordinate-in α n hα hn

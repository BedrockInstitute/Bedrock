{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile

module K8.Controls
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
open import CodedVocabulary 𝒮 using ( refinesΔ )
import K8.Cohen
module C = K8.Cohen 𝒮 ext paths pair un pow sep κ w

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

assigned-one-excludes-zero : (α n p q : S)
  → ⟨ α ∈ˢ κ ⟩ → ⟨ n ∈ˢ w ⟩
  → ⟨ p ∈ˢ C.carrier ⟩ → ⟨ q ∈ˢ C.carrier ⟩
  → ⟨ refinesΔ C.order q p ⟩
  → ⟨ refinesΔ p (C.coordinate α n) C.bit₁ ⟩
  → ⟨ refinesΔ q (C.coordinate α n) C.bit₀ ⟩
  → ⟨ ⊥ ⟩
assigned-one-excludes-zero α n p q hα hn hp hq hqp one zeroValue =
  C.bits-distinct (snd (subst ⟨_⟩ (C.PM.carrier-spec q) hq)
    (C.coordinate α n) (C.coordinate-in α n hα hn)
    C.bit₀ C.bit₀-in C.bit₁ C.bit₁-in
    (zeroValue , C.MO.refines-mono p q (C.coordinate α n) C.bit₁
      (subst ⟨_⟩ (C.PC.refines-spec q p hq hp) hqp) one))

opposite-points-distinct : (α n : S) → ⟨ α ∈ˢ κ ⟩ → ⟨ n ∈ˢ w ⟩
  → C.MO.point (C.coordinate α n) C.bit₀ ≡ C.MO.point (C.coordinate α n) C.bit₁
  → ⟨ ⊥ ⟩
opposite-points-distinct α n hα hn eq =
  assigned-one-excludes-zero α n p q hα hn hp hq
    (subst ⟨_⟩ (sym (C.PC.refines-spec q p hq hp))
      (λ z hz → subst (λ t → ⟨ z ∈ˢ t ⟩) (sym eq) hz))
    (C.MO.point-refines x C.bit₁) (C.MO.point-refines x C.bit₀)
  where
  x : S
  x = C.coordinate α n
  p q : S
  p = C.MO.point x C.bit₁
  q = C.MO.point x C.bit₀
  hp : ⟨ p ∈ˢ C.carrier ⟩
  hp = C.MO.point-in-carrier x C.bit₁ (C.coordinate-in α n hα hn) C.bit₁-in
  hq : ⟨ q ∈ˢ C.carrier ⟩
  hq = C.MO.point-in-carrier x C.bit₀ (C.coordinate-in α n hα hn) C.bit₀-in

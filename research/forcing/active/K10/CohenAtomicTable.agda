{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import NameSupport
import OrdinaryProfile
import K4.AtomicGraph
import K9.BooleanAtomic
import K10.CohenTableReading

module K10.CohenAtomicTable
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (families : NameKernel.Families 𝒮)
  (accessible : NameKernel.Accessibility 𝒮)
  (images : NameKernel.MemberImage 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (κ w : ZFStructure.S 𝒮)
  (lem : LEM ℓ)
  (paths : (x y : ZFStructure.S 𝒮)
         → (ZFStructure._≈ˢ_ 𝒮 x y) ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  where

open import FOL.ZFStructure using ( module hPropStructure )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

module BAT = K9.BooleanAtomic 𝒮 families accessible images pow κ w lem
  using ( B ; module Atomic )
module AG = K4.AtomicGraph 𝒮 paths using ( entryΔ )
module CTR = K10.CohenTableReading 𝒮 families accessible images pow κ w lem paths

module EQTable (C : S) where

  eq-value : S → S → S
  eq-value x y = fst (BAT.Atomic._≈ᴮ_ x y)

  module R = CTR.Readout C eq-value

  eq-value-in-B : (x y : S) → ⟨ eq-value x y ∈ˢ BAT.B ⟩
  eq-value-in-B x y = snd (BAT.Atomic._≈ᴮ_ x y)

  read-eq : (x y b : S)
    → ⟨ AG.entryΔ R.G.graphH x y b ⟩
    → ⟨ x ∈ˢ C ⟩ × ⟨ y ∈ˢ C ⟩ × (b ≡ eq-value x y)
  read-eq x y b h = R.entryΔ-to x y b h

  atomic-total : (x y : S) → ⟨ x ∈ˢ C ⟩ → ⟨ y ∈ˢ C ⟩
    → Σ[ b ∈ S ] (⟨ b ∈ˢ BAT.B ⟩ × ⟨ AG.entryΔ R.G.graphH x y b ⟩)
  atomic-total x y hx hy =
    eq-value x y ,
    ( eq-value-in-B x y
    , R.entryΔ-from x y (eq-value x y) hx hy refl )

  atomic-range : (x y b : S)
    → ⟨ AG.entryΔ R.G.graphH x y b ⟩ → ⟨ b ∈ˢ BAT.B ⟩
  atomic-range x y b h =
    subst (λ w → ⟨ w ∈ˢ BAT.B ⟩) (sym (snd (snd (read-eq x y b h))))
      (eq-value-in-B x y)

  atomic-unique : (x y b b' : S)
    → ⟨ AG.entryΔ R.G.graphH x y b ⟩
    → ⟨ AG.entryΔ R.G.graphH x y b' ⟩
    → b ≡ b'
  atomic-unique x y b b' h h' =
    (snd (snd (read-eq x y b h))) ∙
      (sym (snd (snd (read-eq x y b' h'))))

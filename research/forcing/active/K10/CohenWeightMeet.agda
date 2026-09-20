{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile
import K4.Algebra
import K4.Implication
import K9.BooleanAtomic

module K10.CohenWeightMeet
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
open K4.Algebra 𝒮 using ( Pt ; _≤ᴮ_ )

module BAT = K9.BooleanAtomic 𝒮 families accessible images pow κ w lem
  using ( B ; weight ; weight-least ; module NG ; module IC ; module BK )
module LAT = K4.Algebra.Lattice BAT.IC.codedLattice
  using ( _⊓ᴮ_ )
open module IMP = K4.Implication 𝒮 BAT.NG.extensional BAT.NG.≈ˢ-paths BAT.B
  BAT.IC.codedLattice BAT.IC.codedComplement
  using ( _⇒ᴮ_ ; ⇒ᴮ-curry ; ⇒ᴮ-uncurry ; ⊓-comm )

weight-meet-promote : (n z : S) (b c : Pt BAT.B)
  → ((a : Pt BAT.B) → ⟨ BAT.BK.entry z (fst a) ∈ˢ n ⟩
      → ⟨ (b LAT.⊓ᴮ a) ≤ᴮ c ⟩)
  → ⟨ (b LAT.⊓ᴮ BAT.weight n z) ≤ᴮ c ⟩
weight-meet-promote n z b c hyp =
  subst (λ t → ⟨ t ≤ᴮ c ⟩) (⊓-comm (BAT.weight n z) b) wtmeet
  where
  acurry : (a : Pt BAT.B)
    → ⟨ BAT.BK.entry z (fst a) ∈ˢ n ⟩
    → ⟨ a ≤ᴮ (b IMP.⇒ᴮ c) ⟩
  acurry a ha = ⇒ᴮ-curry a b c
    (subst (λ t → ⟨ t ≤ᴮ c ⟩) (⊓-comm b a) (hyp a ha))
  wtcurry : ⟨ BAT.weight n z ≤ᴮ (b IMP.⇒ᴮ c) ⟩
  wtcurry = BAT.weight-least n z (b IMP.⇒ᴮ c) acurry
  wtmeet : ⟨ (BAT.weight n z LAT.⊓ᴮ b) ≤ᴮ c ⟩
  wtmeet = ⇒ᴮ-uncurry (BAT.weight n z) b c wtcurry

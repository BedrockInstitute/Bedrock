{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile
import K4.Algebra
import K4.Implication
import K4.Substitution
import K9.BooleanAtomic
import K9.NameGround
import K10.CohenValSeam

module K10.CohenBooleanSubst
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

module NG = K9.NameGround 𝒮 families accessible images pow κ w
  using ( extensional ; ≈ˢ-paths )
module BAT = K9.BooleanAtomic 𝒮 families accessible images pow κ w lem
  using ( B ; module Atomic ; module IC ; module BK ; module Laws )
open K4.Algebra 𝒮 using ( Pt ; _≤ᴮ_ ; ⊆ˢ-trans )
open K4.Algebra.Lattice BAT.IC.codedLattice using ( _⊓ᴮ_ )
open K4.Implication 𝒮 NG.extensional NG.≈ˢ-paths BAT.B
  BAT.IC.codedLattice BAT.IC.codedComplement
  using ( ⊓-comm ; ⊤-greatest )
module VS = K10.CohenValSeam 𝒮 families accessible images pow κ w lem paths

open BAT.Atomic using () renaming ( _≈ᴮ_ to eq ; _∈ᴮ_ to mem )

≈ᴮ-congˡ : (m n p : S) → ⟨ (eq m n ⊓ᴮ eq m p) ≤ᴮ eq n p ⟩
≈ᴮ-congˡ m n p =
  subst (λ c → ⟨ (c ⊓ᴮ eq m p) ≤ᴮ eq n p ⟩)
    (BAT.Atomic.≈ᴮ-sym n m) (BAT.Laws.≈ᴮ-trans n m p)

≈ᴮ-congʳ : (m n p : S) → ⟨ (eq n p ⊓ᴮ eq m n) ≤ᴮ eq m p ⟩
≈ᴮ-congʳ m n p =
  subst (λ z → ⟨ z ≤ᴮ eq m p ⟩) (⊓-comm (eq m n) (eq n p))
    (BAT.Laws.≈ᴮ-trans m n p)

module SubCore = K4.Substitution.Core 𝒮 NG.extensional NG.≈ˢ-paths
  BAT.B BAT.IC.codedLattice BAT.IC.codedComplement BAT.BK.IsName

module SubLaws = SubCore.Laws
  eq mem
  BAT.Laws.≈ᴮ-refl BAT.Atomic.≈ᴮ-sym
  BAT.Laws.∈ᴮ-congˡ BAT.Laws.∈ᴮ-congʳ
  ≈ᴮ-congˡ ≈ᴮ-congʳ
  VS.val
  VS.law-∈ VS.law-≐ VS.law-∧ VS.law-∨ VS.law-⇒ VS.law-⊥
  VS.law-∃-ub VS.law-∃-lub VS.law-∀-lb VS.law-∀-glb
  VS.law-∃∈-ub VS.law-∃∈-lub VS.law-∀∈-lb VS.law-∀∈-glb

subst-head = SubLaws.subst-head
subst₁ = SubLaws.subst₁

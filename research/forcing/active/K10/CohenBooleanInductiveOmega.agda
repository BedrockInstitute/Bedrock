{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile
import CardinalBridge
import K4.Algebra
import K4.Implication
import K9.BooleanAtomic
import K9.NameGround
import K10.CohenBooleanSuccApply

module K10.CohenBooleanInductiveOmega
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (families : NameKernel.Families 𝒮)
  (accessible : NameKernel.Accessibility 𝒮)
  (images : NameKernel.MemberImage 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (κ w : ZFStructure.S 𝒮)
  (lem : LEM ℓ)
  (hw : ⟨ CardinalBridge.isOmega 𝒮 w ⟩)
  (paths : (x y : ZFStructure.S 𝒮)
         → (ZFStructure._≈ˢ_ 𝒮 x y) ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  where

open import FOL.ZFStructure using ( module hPropStructure )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

module NG = K9.NameGround 𝒮 families accessible images pow κ w
  using ( extensional ; ≈ˢ-paths ; chk-name )
module BAT = K9.BooleanAtomic 𝒮 families accessible images pow κ w lem
  using ( B ; module Atomic ; module IC )
open K4.Algebra 𝒮 using ( Pt ; _≤ᴮ_ )
open K4.Algebra.Lattice BAT.IC.codedLattice using ( _⊓ᴮ_ ; ⊤ᴮ )
open K4.Implication 𝒮 NG.extensional NG.≈ˢ-paths BAT.B
  BAT.IC.codedLattice BAT.IC.codedComplement
  using ( ≤ᴮ-antisym ; ⊤-greatest ; ⊓-⊤ )
module Ap = K10.CohenBooleanSuccApply 𝒮 families accessible images pow
  κ w lem hw paths

open Ap using ( indSrc ; inductive-at-check )
open Ap.Ind using ( checkNm ; emptyEnv )
open BAT.Atomic using () renaming ( _≈ᴮ_ to eq )

omegaNm : Ap.Ind.VS.Nameᴮ
omegaNm =
  Ap.Ind.BNG.translated-check w
  , Ap.Ind.BNG.Translation.trᴮ-name
      (Ap.Ind.BNG.NG.Check.chk w)
      (NG.chk-name w)

check≈omega : eq (Ap.Ind.BNG.Checked.check w) (Ap.Ind.BNG.translated-check w)
              ≡ ⊤ᴮ
check≈omega =
  BAT.Atomic.≈ᴮ-sym (Ap.Ind.BNG.Checked.check w)
    (Ap.Ind.BNG.translated-check w)
  ∙ Ap.Ind.BNG.translated-check-comparison w

opaque
  inductive-at-omega : Ap.Ind.VS.val indSrc (omegaNm ∷ emptyEnv) ≡ ⊤ᴮ
  inductive-at-omega = ≤ᴮ-antisym
    (⊤-greatest (Ap.Ind.VS.val indSrc (omegaNm ∷ emptyEnv)))
    (subst (λ z → ⟨ z ≤ᴮ Ap.Ind.VS.val indSrc (omegaNm ∷ emptyEnv) ⟩)
      (cong₂ _⊓ᴮ_ check≈omega inductive-at-check ∙ ⊓-⊤ ⊤ᴮ)
      (Ap.Sub.subst₁ indSrc (checkNm w) omegaNm))

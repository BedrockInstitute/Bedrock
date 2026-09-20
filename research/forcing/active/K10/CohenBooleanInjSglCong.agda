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
import K10.CohenBooleanInjSgl
import K10.CohenBooleanSubst

-- Transfer IsSingletonφ / IsPairφ along ≈ᴮ at the head, via subst-head.
-- Load is InjSgl + Subst, matching SuccApply (Inductive + Subst).
-- No extra ValSeam instance. No CCC, Force, Pipe, Miximal, or OmegaTop.

module K10.CohenBooleanInjSglCong
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
  using ( B ; module Atomic ; module IC )
open K4.Algebra 𝒮 using ( _≤ᴮ_ )
open K4.Algebra.Lattice BAT.IC.codedLattice using ( _⊓ᴮ_ ; ⊤ᴮ )
open K4.Implication 𝒮 NG.extensional NG.≈ˢ-paths BAT.B
  BAT.IC.codedLattice BAT.IC.codedComplement
  using ( ⊓-⊤ )
module Sgl = K10.CohenBooleanInjSgl 𝒮 families accessible images pow κ w lem paths
module Sub = K10.CohenBooleanSubst 𝒮 families accessible images pow κ w lem paths
open BAT.Atomic using () renaming ( _≈ᴮ_ to eq )

open Sgl using ( checkNm ; sglSrc ; pairSrc ; sglEnv ; pairEnv
               ; sgl-at-checks ; pair-at-checks )
open Sgl.BNG.Checked using ( check )

sgl-subst : (t x : S) (σ : Sgl.VS.Nameᴮ)
  → ⟨ (eq (check t) (fst σ) ⊓ᴮ Sgl.VS.val sglSrc (sglEnv t x))
      ≤ᴮ Sgl.VS.val sglSrc (σ ∷ checkNm x ∷ []) ⟩
sgl-subst t x σ = Sub.subst-head sglSrc (checkNm x ∷ []) (checkNm t) σ

sgl-from-eq : (t x : S) (σ : Sgl.VS.Nameᴮ)
  → ⟨ CardinalBridge.isSingleton 𝒮 t x ⟩
  → ⟨ eq (fst σ) (check t)
      ≤ᴮ Sgl.VS.val sglSrc (σ ∷ checkNm x ∷ []) ⟩
sgl-from-eq t x σ hs =
  subst (λ z → ⟨ z ≤ᴮ Sgl.VS.val sglSrc (σ ∷ checkNm x ∷ []) ⟩)
    (⊓-⊤ (eq (check t) (fst σ)) ∙ BAT.Atomic.≈ᴮ-sym (check t) (fst σ))
    (subst (λ z → ⟨ (eq (check t) (fst σ) ⊓ᴮ z)
                    ≤ᴮ Sgl.VS.val sglSrc (σ ∷ checkNm x ∷ []) ⟩)
      (sgl-at-checks t x hs)
      (sgl-subst t x σ))

pair-subst : (t x y : S) (σ : Sgl.VS.Nameᴮ)
  → ⟨ (eq (check t) (fst σ) ⊓ᴮ Sgl.VS.val pairSrc (pairEnv t x y))
      ≤ᴮ Sgl.VS.val pairSrc (σ ∷ checkNm x ∷ checkNm y ∷ []) ⟩
pair-subst t x y σ =
  Sub.subst-head pairSrc (checkNm x ∷ checkNm y ∷ []) (checkNm t) σ

pair-from-eq : (t x y : S) (σ : Sgl.VS.Nameᴮ)
  → ⟨ CardinalBridge.isPair 𝒮 t x y ⟩
  → ⟨ eq (fst σ) (check t)
      ≤ᴮ Sgl.VS.val pairSrc (σ ∷ checkNm x ∷ checkNm y ∷ []) ⟩
pair-from-eq t x y σ hp =
  subst (λ z → ⟨ z ≤ᴮ Sgl.VS.val pairSrc (σ ∷ checkNm x ∷ checkNm y ∷ []) ⟩)
    (⊓-⊤ (eq (check t) (fst σ)) ∙ BAT.Atomic.≈ᴮ-sym (check t) (fst σ))
    (subst (λ z → ⟨ (eq (check t) (fst σ) ⊓ᴮ z)
                    ≤ᴮ Sgl.VS.val pairSrc (σ ∷ checkNm x ∷ checkNm y ∷ []) ⟩)
      (pair-at-checks t x y hp)
      (pair-subst t x y σ))

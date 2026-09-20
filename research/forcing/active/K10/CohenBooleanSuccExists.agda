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
import K10.CohenBooleanInductive
import K10.CohenBooleanRename

module K10.CohenBooleanSuccExists
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
open import FOL.Syntax using ( var ; ∃̇∈ ; ∀̇∈ )
open import FOL.Manipulation.Renaming using ( renameFo )
import CardinalBridge

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

module NG = K9.NameGround 𝒮 families accessible images pow κ w
  using ( extensional ; ≈ˢ-paths )
module BAT = K9.BooleanAtomic 𝒮 families accessible images pow κ w lem
  using ( B ; module Atomic ; module IC )
open K4.Algebra 𝒮 using ( Pt ; _≤ᴮ_ )
open K4.Algebra.Lattice BAT.IC.codedLattice using ( _⊓ᴮ_ ; ⊤ᴮ )
open K4.Implication 𝒮 NG.extensional NG.≈ˢ-paths BAT.B
  BAT.IC.codedLattice BAT.IC.codedComplement
  using ( ≤ᴮ-antisym ; ⊤-greatest ; ⊓-⊤ )
module Ind = K10.CohenBooleanInductive 𝒮 families accessible images pow
  κ w lem hw paths
module RN = K10.CohenBooleanRename 𝒮 families accessible images pow κ w lem paths
module CB = CardinalBridge 𝒮

open Ind using ( checkNm ; emptyEnv ; succSrc ; succEnv ; succ-at-checks )

succInner : Ind.VS.Src 3
succInner = renameFo CB.wk2 succSrc

succExists : Ind.VS.Src 2
succExists = ∃̇∈ (var (suc zero)) succInner

succClause : Ind.VS.Src 1
succClause = ∀̇∈ (var zero) succExists

rename-wk2 : (m n : ZFStructure.S 𝒮)
  → RN.renameEnv CB.wk2 (checkNm m ∷ checkNm n ∷ checkNm w ∷ emptyEnv)
    ≡ succEnv m n
rename-wk2 m n = refl

succ-rename : (m n : ZFStructure.S 𝒮)
  → Ind.VS.val succInner (checkNm m ∷ checkNm n ∷ checkNm w ∷ emptyEnv)
    ≡ Ind.VS.val succSrc (succEnv m n)
succ-rename m n =
  RN.val-rename CB.wk2 succSrc (checkNm m ∷ checkNm n ∷ checkNm w ∷ emptyEnv)
  ∙ cong (Ind.VS.val succSrc) (rename-wk2 m n)

opaque
  succ-exists-at-check : (m n : ZFStructure.S 𝒮)
    → ⟨ m ∈ˢ w ⟩ → ⟨ CB.isSuccOf m n ⟩
    → Ind.VS.val succExists (checkNm n ∷ checkNm w ∷ emptyEnv) ≡ ⊤ᴮ
  succ-exists-at-check m n hin hsucc = ≤ᴮ-antisym
    (⊤-greatest (Ind.VS.val succExists (checkNm n ∷ checkNm w ∷ emptyEnv)))
    (subst (λ z → ⟨ z ≤ᴮ Ind.VS.val succExists (checkNm n ∷ checkNm w ∷ emptyEnv) ⟩)
      (cong₂ _⊓ᴮ_ (Ind.CM.check-∈-top m w hin)
        (succ-rename m n ∙ succ-at-checks m n hsucc) ∙ ⊓-⊤ ⊤ᴮ)
      (Ind.VS.law-∃∈-ub (suc zero) succInner
        (checkNm n ∷ checkNm w ∷ emptyEnv) (checkNm m)))

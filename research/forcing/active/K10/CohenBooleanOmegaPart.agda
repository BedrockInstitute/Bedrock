{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile
import CardinalBridge
import K10.CohenBooleanNotCH
import K10.CohenBooleanRename
import K10.CohenBooleanOmegaEq
import K10.CohenBooleanOmegaTop
import K10.CohenBooleanOmegaSrc

module K10.CohenBooleanOmegaPart
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (families : NameKernel.Families 𝒮)
  (accessible : NameKernel.Accessibility 𝒮)
  (images : NameKernel.MemberImage 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (find : OrdinaryProfile.FoundationInduction 𝒮)
  (κ w : ZFStructure.S 𝒮)
  (lem : LEM ℓ)
  (hw : ⟨ CardinalBridge.isOmega 𝒮 w ⟩)
  (paths : (x y : ZFStructure.S 𝒮)
         → (ZFStructure._≈ˢ_ 𝒮 x y) ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  where

open import Cubical.Data.Sigma using ( Σ≡Prop )
open import FOL.Manipulation.ConstantOccurrences using ( module ZeroOccurrences )
open import FOL.Manipulation.Renaming using ( renameFo )
import CardinalBridge

module CH = K10.CohenBooleanNotCH 𝒮 families accessible images pow find
  κ w lem hw paths
  using ( module VS ; module CH ; module BNG ; CH-omega-part ; omegaNm ; at2 ; emptyEnv ; ⊤B )
module RN = K10.CohenBooleanRename 𝒮 families accessible images pow κ w lem paths
  using ( renameEnv ; val-rename )
module CB = CardinalBridge 𝒮
module ZO = ZeroOccurrences (ZFStructure.S 𝒮)

omegaSrc1 : CH.VS.Src 1
omegaSrc1 = ZO.erase CB.IsOmegaφ refl

erase-rename : CH.CH-omega-part ≡ renameFo CH.CH.om-w omegaSrc1
erase-rename = refl

om-w-env : (pω : CH.VS.Nameᴮ)
  → RN.renameEnv CH.CH.om-w (CH.at2 pω) ≡ (CH.omegaNm ∷ CH.emptyEnv)
om-w-env pω = refl

omega-part-val : (pω : CH.VS.Nameᴮ)
  → CH.VS.val CH.CH-omega-part (CH.at2 pω)
    ≡ CH.VS.val omegaSrc1 (CH.omegaNm ∷ CH.emptyEnv)
omega-part-val pω =
  cong (λ φ → CH.VS.val φ (CH.at2 pω)) erase-rename
  ∙ RN.val-rename CH.CH.om-w omegaSrc1 (CH.at2 pω)
  ∙ cong (CH.VS.val omegaSrc1) (om-w-env pω)

module Omega = K10.CohenBooleanOmegaEq 𝒮 families accessible images pow
  κ w lem hw paths using ( omegaSrc-eq )
module Top = K10.CohenBooleanOmegaTop 𝒮 families accessible images pow
  κ w lem hw paths using ( omega-at-omega ; omegaNm )
module Source = K10.CohenBooleanOmegaSrc 𝒮 using ( omegaSrc-erase )

omega-name-agrees : Top.omegaNm ≡ CH.omegaNm
omega-name-agrees = Σ≡Prop (λ x → snd (CH.BNG.BK.IsName x)) refl

omega-part-top : (pω : CH.VS.Nameᴮ)
  → CH.VS.val CH.CH-omega-part (CH.at2 pω) ≡ CH.⊤B
omega-part-top pω = omega-part-val pω
  ∙ cong (λ σ → CH.VS.val omegaSrc1 (σ ∷ CH.emptyEnv)) (sym omega-name-agrees)
  ∙ cong (λ φ → CH.VS.val φ (Top.omegaNm ∷ CH.emptyEnv))
      (sym (Omega.omegaSrc-eq ∙ Source.omegaSrc-erase))
  ∙ Top.omega-at-omega

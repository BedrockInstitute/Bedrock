{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile
import CardinalBridge
import K7.ChainConditions
import K8.CohenCCC
import K9.NameGround
import K10.CohenBooleanInjBot

module K10.CohenBooleanInjCcc
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

open import OrdinaryProfile 𝒮 using ( ChoiceSet )
open NameKernel.Families families using ( hasCollect )

module IB = K10.CohenBooleanInjBot 𝒮 families accessible images pow κ w lem paths
module NG = K9.NameGround 𝒮 families accessible images pow κ w
  using ( extensional ; ≈ˢ-paths ; hasPair ; hasUnion ; hasSeparation ; module C )
module CH = K7.ChainConditions 𝒮 NG.extensional NG.≈ˢ-paths
  using ( CCC₂ᴵ )

module Over (choice : ChoiceSet) where

  module CCC = K8.CohenCCC.AtOmega 𝒮
    NG.extensional NG.≈ˢ-paths NG.hasPair NG.hasUnion pow
    NG.hasSeparation hasCollect find κ w lem choice hw

  cohen-ccc : ⟨ CH.CCC₂ᴵ NG.C.carrier NG.C.order w ⟩
  cohen-ccc = CCC.ccc

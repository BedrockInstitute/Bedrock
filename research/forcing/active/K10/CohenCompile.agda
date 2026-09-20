{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile
import NameSpace
import K4.Algebra
import K5.InstanceValue
import K9.NameGround
import K9.BooleanAtomic
import K10.CohenDomain

module K10.CohenCompile
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
open K4.Algebra 𝒮 using ( Pt )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

module NG = K9.NameGround 𝒮 families accessible images pow κ w
  using ( extensional ; ≈ˢ-paths ; hasSeparation ; module C )
module BAT = K9.BooleanAtomic 𝒮 families accessible images pow κ w lem
  using ( B ; module Atomic ; module BK )
module NS = NameSpace 𝒮
module NSB = NS.Instantiate families accessible BAT.B
module CD = K10.CohenDomain 𝒮 families accessible images pow κ w lem paths
module IV = K5.InstanceValue 𝒮 NG.extensional pow NG.hasSeparation NG.≈ˢ-paths
  NG.C.presentation NG.C.laws

open CD.G.AtomicGraph CD.atomicGraph

module Comp = IV.Compiler
  BAT.BK.IsName
  NS.nameAtˢ NS.nameΔ NS.nameAtˢ-reading
  NSB.name-adequate
  BAT.Atomic._≈ᴮ_ BAT.Atomic._∈ᴮ_
  eqAtˢ memAtˢ eqΔ memΔ
  eqAtˢ-reading memAtˢ-reading
  eq-sound eq-total mem-sound mem-total

Src : ℕ → Type ℓ
Src = Comp.Src

Nameᴮ : Type ℓ
Nameᴮ = Comp.Nameᴮ

Envᴮ : ℕ → Type ℓ
Envᴮ = Comp.Envᴮ

val : ∀ {k} → Src k → Envᴮ k → Pt BAT.B
val = Comp.val

valLaws : Comp.VC.InterpLaws
valLaws = Comp.valLaws

open Comp.VC.InterpLaws valLaws public

{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile
import GroundDescription
import K4.Algebra
import K4.Implication
import K4.ValueSets
import K9.BooleanNameGround
import K9.BooleanAtomic
import K9.NameGround

module K10.CohenBooleanSubset
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (families : NameKernel.Families 𝒮)
  (accessible : NameKernel.Accessibility 𝒮)
  (images : NameKernel.MemberImage 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (κ w : ZFStructure.S 𝒮)
  (lem : LEM ℓ)
  where

open import FOL.ZFStructure using ( module hPropStructure )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

module Ground = K9.NameGround 𝒮 families accessible images pow κ w
module BNG = K9.BooleanNameGround 𝒮 families accessible images pow κ w lem
open BNG using ( B ; weight ; module NG ; module IC ; module BK
               ; module BSupport ; module Translation )
open NG using ( extensional ; ≈ˢ-paths )
open K4.Algebra 𝒮 using ( Pt )
open K4.Algebra.CodedComplete IC.codedComplete using ( infᴮ )
open K4.Implication 𝒮 extensional ≈ˢ-paths B IC.codedLattice IC.codedComplement
  using ( _⇒ᴮ_ )
module BAT = K9.BooleanAtomic.Atomic 𝒮 families accessible images pow κ w lem
  using ( _∈ᴮ_ )
open NameKernel.MemberImage images using ( image ; image-spec )
module GD = GroundDescription 𝒮 extensional ≈ˢ-paths

module VS = K4.ValueSets.Core 𝒮 extensional ≈ˢ-paths B IC.codedLattice
  IC.codedComplete
  using ( member→values ; module ValueSets )
private
  values = VS.member→values image image-spec
  module Values = VS.ValueSets values

tau : S
tau = Translation.trᴮ (NG.Check.chk w)

omegaNm : Σ[ x ∈ S ] ⟨ BK.IsName x ⟩
omegaNm = tau , Translation.trᴮ-name (NG.Check.chk w) (Ground.chk-name w)

subsetFam : (σ : S) → Pt (BSupport.support σ) → Pt B
subsetFam σ x = (weight σ (fst x)) ⇒ᴮ (BAT._∈ᴮ_ (fst x) tau)

subsetVal : S → Pt B
subsetVal σ = infᴮ (Values.attain (BSupport.support σ) (subsetFam σ))
  (Values.attain-sub (BSupport.support σ) (subsetFam σ))

groundPω : S
groundPω = GD.powerOf pow w

powerB : S
powerB = Translation.trᴮ (NG.Check.chk groundPω)

powerNm : Σ[ x ∈ S ] ⟨ BK.IsName x ⟩
powerNm = powerB , Translation.trᴮ-name (NG.Check.chk groundPω)
  (Ground.chk-name groundPω)

opaque
  candEntry : S → S
  candEntry σ = BK.entry (Translation.trᴮ σ) (fst (subsetVal (Translation.trᴮ σ)))

  candWeight : S → S
  candWeight σ = fst (subsetVal (Translation.trᴮ σ))

  candWeight-inB : (σ : S) → ⟨ candWeight σ ∈ˢ B ⟩
  candWeight-inB σ = snd (subsetVal (Translation.trᴮ σ))

  candEntry-weight : (σ : S) → candEntry σ ≡ BK.entry (Translation.trᴮ σ) (candWeight σ)
  candEntry-weight σ = refl

opaque
  unfolding candWeight candWeight-inB
  candWeight-pt : (σ : S)
    → subsetVal (Translation.trᴮ σ) ≡ (candWeight σ , candWeight-inB σ)
  candWeight-pt σ = refl

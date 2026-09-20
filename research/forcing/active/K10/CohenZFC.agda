{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile
import CardinalBridge
import GroundDescription
import ForcingNotion
import K6.FoundationAtStructures
import K6.GroundTransferAtStructures
import Cubical.HITs.PropositionalTruncation as PT
import K9.NameGround
import K10.CohenPairUnion

module K10.CohenZFC
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (families : NameKernel.Families 𝒮)
  (accessible : NameKernel.Accessibility 𝒮)
  (images : NameKernel.MemberImage 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (κ w : ZFStructure.S 𝒮)
  (hw : ⟨ CardinalBridge.isOmega 𝒮 w ⟩)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open PT using ( ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

module Ground = K9.NameGround 𝒮 families accessible images pow κ w
module GD = GroundDescription 𝒮 Ground.extensional Ground.≈ˢ-paths
module PU = K10.CohenPairUnion 𝒮 families accessible images pow κ w
module OP = OrdinaryProfile 𝒮
module CB = CardinalBridge 𝒮

ground-infinity : OP.Infinity
ground-infinity =
  ∣ w , hw .fst .fst , (λ x hx → PT.map (take-member x) (hw .fst .snd x hx)) ∣₁
  where
  take-member : (x : S) → Σ[ y ∈ S ] ⟨ (y ∈ˢ w) ⊓ CB.isSuccOf y x ⟩
              → Σ[ y ∈ S ] ⟨ (y ∈ˢ w) ⊓ (x ∈ˢ y) ⟩
  take-member x (y , hy , sc) = y , hy , sc .fst

module FoundSeam = K6.FoundationAtStructures.Seam 𝒮
  Ground.K.entry Ground.K.Child Ground.K.isPropChild
  (λ x b n h → ∣ b , h ∣₁) Ground.K.child-wf Ground.GS.empty Ground.empty-spec
  Ground.C.carrier Ground.P._≼_ Ground.P.≼-refl
  (λ {p} {q} {r} → Ground.P.≼-trans {p} {q} {r}) Ground.P.nonempty
  Ground.K.IsName Ground.K.child-is-name

module InfSeam = K6.GroundTransferAtStructures.Seam 𝒮
  Ground.K.entry Ground.K.Child Ground.K.isPropChild
  (λ x b n h → ∣ b , h ∣₁) Ground.K.child-wf Ground.GS.empty Ground.empty-spec
  Ground.C.carrier Ground.P._≼_ Ground.P.≼-refl
  (λ {p} {q} {r} → Ground.P.≼-trans {p} {q} {r}) Ground.P.nonempty
  Ground.K.IsName Ground.K.child-is-name

module AtGeneric (G : Ground.P.Sub) where

  module Found = FoundSeam.At G
  module Inf = InfSeam.AtG G Ground.K.entry-inj Ground.≈ˢ-paths GD.ext-path
    Ground.Check.chk Ground.Check.chk-spec Ground.genericName Ground.generic-spec
    Ground.chk-name ground-infinity
  module PairU = PU.AtGeneric G

  extension : ZFStructure (hPropAlgebra ℓ)
  extension = Ground.PS.𝒮ᴾ[ G ]

  module Profile = OrdinaryProfile extension

  extensional : Profile.Extensionality
  extensional = Ground.PS.P.Ext.extensional G

  foundation : Profile.FoundationInduction
  foundation = Found.foundation

  infinity : ⟨ Ground.P.positive G ⟩ → Profile.Infinity
  infinity = Inf.hasInfinity

  module Assemble
    (power : Profile.PowerSet)
    (separation : Profile.Separation)
    (replacement : Profile.Collection)
    (choice : Profile.ChoiceSet)
    (fil : Ground.P.isFilter G)
    where

    private
      pos : ⟨ Ground.P.positive G ⟩
      pos = Ground.P.isFilter.inhabited fil

    ordinaryZF : Profile.OrdinaryZF
    ordinaryZF = record
      { extensional    = extensional
      ; hasPair        = PairU.hasPairᶠ fil
      ; hasUnion       = PairU.hasUnionᶠ fil
      ; hasPower       = power
      ; hasInfinity    = infinity pos
      ; hasSeparation  = separation
      ; hasReplacement = replacement
      ; foundation     = foundation }

    ordinaryZFC : Profile.OrdinaryZFC
    ordinaryZFC = record
      { zf = ordinaryZF
      ; hasChoice = choice }

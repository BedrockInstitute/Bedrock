{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile
import Cubical.HITs.PropositionalTruncation as PT
import NameSpace
import K6.NameBuildAtGround
import K6.ElementaryAtNames
import K9.NameGround
import CodedVocabulary

module K10.CohenPairUnion
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (families : NameKernel.Families 𝒮)
  (accessible : NameKernel.Accessibility 𝒮)
  (images : NameKernel.MemberImage 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (κ w : ZFStructure.S 𝒮)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import CodedVocabulary 𝒮 using ( refinesΔ )
open PT using ( ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

module Ground = K9.NameGround 𝒮 families accessible images pow κ w
module NP = NameSpace 𝒮
module NB = K6.NameBuildAtGround.Seam 𝒮 families accessible Ground.C.carrier

≼-reading : (p q : Ground.P.Cond)
  → (p Ground.P.≼ q) ≡ refinesΔ Ground.C.order (fst p) (fst q)
≼-reading p q = refl

module Elem = K6.ElementaryAtNames.Compose 𝒮
  Ground.K.entry Ground.K.Child Ground.K.isPropChild
  (λ x b n h → ∣ b , h ∣₁) Ground.K.child-wf Ground.GS.empty Ground.empty-spec
  Ground.C.carrier Ground.P._≼_ Ground.P.≼-refl
  (λ {p} {q} {r} → Ground.P.≼-trans {p} {q} {r}) Ground.P.nonempty
  Ground.K.IsName Ground.K.child-is-name
  Ground.K.entry-inj Ground.K.entry-isKPair NB.PI.CR.kpair-unique
  Ground.≈ˢ-paths Ground.C.order ≼-reading
  NB.K.pairOf NB.K.pairOf-spec NB.BG.⋃ᴳ NB.BG.⋃ᴳ-in NB.BG.support-bound
  NB.GD.ext-path NB.NI.colAt NB.NI.colAt-reading
  NB.GD.separateOf NB.GD.separateOf-spec NB.imageOfGraph NB.BG.⋃ᴳ-spec
  (λ x n e → e) Ground.K.name-intro NB.BG.support
  NB.PI.nameBound NB.PI.nameBound-contains
  (NP.nameAtˢ zero (suc zero))
  NB.PI.name-adequate Ground.hasCollect Ground.hasSeparation

module AtGeneric (G : Ground.P.Sub) where

  module E = Elem.AtG G

  hasPair : ⟨ Ground.P.positive G ⟩ → OrdinaryProfile.Pairing (Ground.PS.𝒮ᴾ[ G ])
  hasPair = E.hasPair

  hasPairᶠ : Ground.P.isFilter G → OrdinaryProfile.Pairing (Ground.PS.𝒮ᴾ[ G ])
  hasPairᶠ = E.hasPairᶠ

  hasUnionᶠ : Ground.P.isFilter G → OrdinaryProfile.Union (Ground.PS.𝒮ᴾ[ G ])
  hasUnionᶠ = E.hasUnionᶠ

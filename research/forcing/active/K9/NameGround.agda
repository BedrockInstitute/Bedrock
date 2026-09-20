{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile

module K9.NameGround
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (families : NameKernel.Families 𝒮)
  (accessible : NameKernel.Accessibility 𝒮)
  (images : NameKernel.MemberImage 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (κ w : ZFStructure.S 𝒮)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )
import GroundDescription
import StandardNames
import CodedCompletion
import ForcingNotion
import K5.Structures
import K8.GroundSets
import K8.FiniteUnion
import K8.Cohen

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open NameKernel.Families families public using ( sets; hasCollect )
open NameKernel.Sets sets public using ( core; hasUnion; hasSeparation )
open NameKernel.Core core public using ( extensional; hasPair; ≈ˢ-paths )

module GS = K8.GroundSets.Ground 𝒮 extensional ≈ˢ-paths hasPair hasUnion pow hasSeparation κ
  using ( empty; empty-out; separator; separator-spec
        ; ordered; ordered-witness; ≈→≡; pairOf; pairOf-inˡ; pairOf-inʳ; pairOf-out )
module Union = K8.FiniteUnion 𝒮 extensional ≈ˢ-paths hasPair hasUnion pow hasSeparation κ
  using ( bigUnion; bigUnion-spec )
module C = K8.Cohen 𝒮 extensional ≈ˢ-paths hasPair hasUnion pow hasSeparation κ w
  using ( carrier; order; presentation; laws; coordinate; coordinate-in; coordinates; two; bit₀; bit₁
        ; bit₀-in; bit₁-in; bits-distinct )
module K = NameKernel.Kernel 𝒮 core accessible C.carrier
  using ( entry; entry-inj; entry-isKPair; singleOf; singleOf-spec; singleOf-member
        ; Child; isPropChild; child-wf; IsName; Shape; name-intro; child-is-name; Name )
private module Description = GroundDescription 𝒮 extensional ≈ˢ-paths

private
  module Standard = StandardNames.Kernel 𝒮 K.entry K.entry-inj
    K.singleOf K.singleOf-spec K.singleOf-member K.Child
    (λ x n Q h f → PT.rec (snd Q) (λ { (p , hp) → f p hp }) h)
    ≈ˢ-paths Description.ext-path

private module Valid = Standard.Validity C.carrier K.Shape (λ n h → h) K.IsName K.name-intro
open Valid public using ( entries-name )

module Image = Standard.Weighted accessible
  (NameKernel.MemberImage.image images) (NameKernel.MemberImage.image-spec images)
  Union.bigUnion Union.bigUnion-spec using ( imageOn; imageOn-spec; module Over )
module Check = Image.Over C.carrier using ( chk; chk-spec; spread; spread-spec; module Valid )
private module CheckValid = Check.Valid C.carrier K.IsName entries-name (λ p hp → hp)
open CheckValid public using ( chk-name )

opaque
  genericName : S
  genericName = Image.imageOn C.carrier (λ p → K.entry (Check.chk p) p)

  generic-spec : (e : S) → (e ∈ˢ genericName)
    ≡ ⋁ S (λ p → (p ∈ˢ C.carrier) ⊓ (e ≈ˢ K.entry (Check.chk p) p))
  generic-spec = Image.imageOn-spec C.carrier (λ p → K.entry (Check.chk p) p)

empty-spec : (z : S) → (z ∈ˢ GS.empty) ≡ ⊥
empty-spec z = ⇔toPath (GS.empty-out z) Empty.rec*

private module Coded = CodedCompletion.Coded 𝒮 C.presentation using ( decode )
notion : ForcingNotion.ForcingNotion {ℓ}
notion = Coded.decode C.laws
module P = ForcingNotion.Structure notion
private module Order = ForcingNotion.ForcingNotion notion

private
  module Kernel = K5.Structures.Kernel 𝒮 K.entry K.Child K.isPropChild
    (λ x b n h → ∣ b , h ∣₁) K.child-wf GS.empty empty-spec
module PS = Kernel.PosetSide C.carrier Order._≼_ Order.≼-refl
  (λ {p} {q} {r} → Order.≼-trans {p} {q} {r}) Order.nonempty
  K.IsName K.child-is-name using ( Nameᴾ; 𝒮ᴾ[_]; module P )

module AtGeneric (G : P.Sub) where
  module E = PS.P.Ext G using ( _≈[G]_; _∈[G]_; ‖Active‖; entry-value; active-value
    ; ≈-refl; ≈-sym; ≈-trans; ≈-intro; ∈-congˡ; ∈-congʳ; value-extensional )
  module Copy = PS.P.Ext.Copy G K.entry-inj ≈ˢ-paths Description.ext-path
    Check.chk Check.chk-spec genericName generic-spec chk-name
    using ( groundName; module WithPos )

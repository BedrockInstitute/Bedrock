{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
open import FOL.Syntax using ( Formula )
import ForcingNotion
import NameKernel
import OrdinaryProfile
import CodedVocabulary
import K5.Generic
import K5.ExtensionSat
import K9.NameGround
import K9.BooleanNameGround
import K10.CohenAgreement
import K10.CohenReverse

module K10.CohenAgreementSeam
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (families : NameKernel.Families 𝒮)
  (accessible : NameKernel.Accessibility 𝒮)
  (images : NameKernel.MemberImage 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (κ w : ZFStructure.S 𝒮)
  (lem : LEM ℓ)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import CodedVocabulary 𝒮 using ( denseΔ )
open import FOL.ZFModel 𝒮 using ( _⊆ˢ_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

module NG = K9.NameGround 𝒮 families accessible images pow κ w
  using ( core ; extensional ; ≈ˢ-paths ; notion
        ; module C ; module K ; module GS ; empty-spec )
module BG = K9.BooleanNameGround 𝒮 families accessible images pow κ w lem
  using ( B ; entry-agrees ; module Base ; module IC ; module BK ; module Translation )
module Order = ForcingNotion.ForcingNotion NG.notion
module BooleanKernel = NameKernel.Kernel 𝒮 NG.core accessible BG.B
  using ( child-is-name )
module GP = K5.Generic.Poset 𝒮 NG.C.carrier NG.C.order
module GI = GP.Image NG.extensional NG.≈ˢ-paths BG.B BG.IC.codedLattice
  BG.IC.codedComplement BG.IC.codedComplete (BG.Base.codedBase lem)
  using ( Uof ; module FS )
open GI.FS using ( Sub ; Cond ; _∈ᴾ_ ; isFilter )

boolean-child-name : (n : S) → ⟨ BG.BK.IsName n ⟩ → (x : S) → NG.K.Child x n
  → ⟨ BG.BK.IsName x ⟩
boolean-child-name n hn x ch =
  BooleanKernel.child-is-name n hn x
    (PT.map (λ { (b , h) → b , subst (λ e → ⟨ e ∈ˢ n ⟩) (sym (BG.entry-agrees x b)) h })
      ch)

module FromGeneric (G : Sub) (fil : isFilter G)
  (meets : (d : S) → ⟨ d ⊆ˢ NG.C.carrier ⟩
         → ⟨ denseΔ NG.C.carrier NG.C.order d ⟩
         → ⟨ ⋁ Cond (λ q → (q ∈ᴾ G) ⊓ (fst q ∈ˢ d)) ⟩)
  where

  module AGR = K10.CohenAgreement.FromGeneric 𝒮 families accessible images pow κ w lem G fil meets
  module RV = K10.CohenReverse.FromGeneric 𝒮 families accessible images pow κ w lem G
  module EA = K5.ExtensionSat.Transfer.At
    𝒮 NG.K.entry NG.K.Child NG.K.isPropChild (λ x b n h → ∣ b , h ∣₁)
    NG.K.child-wf NG.GS.empty NG.empty-spec
    NG.C.carrier Order._≼_ Order.≼-refl
    (λ {p} {q} {r} → Order.≼-trans {p} {q} {r}) Order.nonempty
    NG.K.IsName NG.K.child-is-name BG.B BG.IC.codedLattice BG.BK.IsName
    boolean-child-name
    G (GI.Uof G)
    using ( _≈[G]_ ; _∈[G]_ ; _≈[U]_ ; _∈[U]_ )

  ≈-agree : (m n : S)
    → (m EA.≈[G] n) ≡ (BG.Translation.trᴮ m EA.≈[U] BG.Translation.trᴮ n)
  ≈-agree = AGR.≈-agree

  ∈-agree : (m n : S)
    → (m EA.∈[G] n) ≡ (BG.Translation.trᴮ m EA.∈[U] BG.Translation.trᴮ n)
  ∈-agree = AGR.∈-agree

  ext-surjective : (n : S) → ⟨ BG.BK.IsName n ⟩
    → Σ[ τ ∈ NG.K.Name ] ⟨ BG.Translation.trᴮ (fst τ) EA.≈[U] n ⟩
  ext-surjective = RV.ext-surjective

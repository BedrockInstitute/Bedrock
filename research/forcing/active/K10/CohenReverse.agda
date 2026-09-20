{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import NameSupport
import OrdinaryProfile
import Valuation
import GroundDescription
import K4.Algebra
import TranslateReverse
import K5.Frame
import K5.Generic
import K5.RoundTrip
import K9.NameGround
import K9.BooleanNameGround
import K10.CohenAgreement

module K10.CohenReverse
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (families : NameKernel.Families 𝒮)
  (accessible : NameKernel.Accessibility 𝒮)
  (images : NameKernel.MemberImage 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (κ w : ZFStructure.S 𝒮)
  (lem : LEM ℓ)
  where

open import FOL.ZFStructure using ( module hPropStructure )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ ; ∥_∥₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

module NG = K9.NameGround 𝒮 families accessible images pow κ w
  using ( core ; sets ; extensional ; ≈ˢ-paths ; entries-name
        ; empty-spec ; module C ; module K ; module GS ; module Union )
module BG = K9.BooleanNameGround 𝒮 families accessible images pow κ w lem
  using ( B ; entry-agrees ; module Base ; module IC ; module BK ; module BSupport
        ; module Translation )
module GD = GroundDescription 𝒮 NG.extensional NG.≈ˢ-paths using ( ext-path )
module Frame = K5.Frame.Poset 𝒮 NG.C.carrier NG.C.order using ( ForcingBase ; module Forcing )
module FB = Frame.ForcingBase (BG.Base.codedBase lem)
  using ( i ; below ; below-sub ; below-in ; below-out )
module BKernel = NameKernel.Kernel 𝒮 NG.core accessible BG.B
  using ( child-is-name )
module ISB = NameSupport.Instantiate.BG 𝒮 NG.sets accessible BG.B
  using ( support-is-join )
module FF = Frame.Forcing NG.extensional NG.≈ˢ-paths BG.B BG.IC.codedLattice
  BG.IC.codedComplement BG.IC.codedComplete (BG.Base.codedBase lem)
  using ( ⊩ᴮ-elim )
open K4.Algebra 𝒮 using ( Pt ; _≤ᴮ_ ; ≤ᴮ-refl ; ⊆ˢ-trans )
module Lattice = K4.Algebra.Lattice BG.IC.codedLattice using ( ⊤ᴮ )
open Lattice using ( ⊤ᴮ )
open BG using ( B )
module GP = K5.Generic.Poset 𝒮 NG.C.carrier NG.C.order
module GI = GP.Image NG.extensional NG.≈ˢ-paths BG.B BG.IC.codedLattice
  BG.IC.codedComplement BG.IC.codedComplete (BG.Base.codedBase lem)
  using ( Uof ; module FS ; module Laws )
open GI.FS using ( Sub ; Cond ; _∈ᴾ_ )
module VU = Valuation.Names.Poset 𝒮 NG.K.entry NG.K.Child NG.K.isPropChild
  (λ x b n h → ∣ b , h ∣₁) NG.K.child-wf NG.GS.empty NG.empty-spec
  B (λ u v → u ≤ᴮ v) ≤ᴮ-refl (λ {u} {v} {w} h k → ⊆ˢ-trans h k) ∣ ⊤ᴮ ∣₁
module CAG = K10.CohenAgreement 𝒮 families accessible images pow κ w lem

module TR = TranslateReverse.Names.Ground.Over 𝒮
  BG.BK.entry BG.BK.entry-inj BG.BK.entry-isKPair BG.BK.Child
  (λ x b n h → ∣ b , h ∣₁)
  (λ x n Q h k → PT.rec (snd Q) (λ { (b , hb) → k b hb }) h)
  BG.BK.child-wf NG.≈ˢ-paths GD.ext-path
  (NameKernel.MemberImage.image images)
  (NameKernel.MemberImage.image-spec images)
  NG.Union.bigUnion NG.Union.bigUnion-spec
  NG.C.carrier BG.B FB.below FB.below-sub
  BG.BSupport.support BG.BSupport.weightsAt
  BG.BSupport.support-out BG.BSupport.entry-in
  (λ n x h → subst ⟨_⟩ (ISB.support-is-join n x) h)
  BG.BSupport.weightsAt-sub BG.BSupport.weight-in BG.BSupport.weight-out

entries-nameᴮ→ᴾ : (n : S)
  → ((e : S) → ⟨ e ∈ˢ n ⟩
     → ∥ Σ[ x ∈ S ] Σ[ p ∈ S ]
         ((e ≡ BG.BK.entry x p) × (⟨ p ∈ˢ NG.C.carrier ⟩ × ⟨ NG.K.IsName x ⟩)) ∥₁)
  → ⟨ NG.K.IsName n ⟩
entries-nameᴮ→ᴾ n listing =
  NG.entries-name n (λ e he →
    PT.map (λ { (x , p , eq , hpc , hx) →
      x , p , subst (λ w → e ≡ w) (BG.entry-agrees x p) eq , hpc , hx })
      (listing e he))

module TRV = TR.Valid BG.BK.IsName BKernel.child-is-name NG.K.IsName
  entries-nameᴮ→ᴾ
  using ( trᴾ-name )

trᴾ-entries-NG : (n e : S) → (e ∈ˢ TR.trᴾ n)
  ≡ ⋁ S (λ x → ⋁ S (λ b → ⋁ ⟨ b ∈ˢ BG.B ⟩ (λ hb → ⋁ S (λ p →
      (NG.K.entry x b ∈ˢ n)
      ⊓ ((p ∈ˢ FB.below (b , hb)) ⊓ (e ≈ˢ NG.K.entry (TR.trᴾ x) p))))))
trᴾ-entries-NG n e =
  TR.trᴾ-entries n e
    ∙ cong (⋁ S)
        (funExt (λ x →
          cong (⋁ S)
            (funExt (λ b →
              cong (⋁ ⟨ b ∈ˢ BG.B ⟩)
                (funExt (λ hb →
                  cong (⋁ S)
                    (funExt (λ p →
                      cong₂ (λ u w → (u ∈ˢ n) ⊓ ((p ∈ˢ FB.below (b , hb)) ⊓ (e ≈ˢ w)))
                        (BG.entry-agrees x b)
                        (BG.entry-agrees (TR.trᴾ x) p)))))))))

module RTC = K5.RoundTrip.Kernel 𝒮 NG.K.entry NG.K.entry-inj NG.K.Child
  (λ x b n h → ∣ b , h ∣₁) NG.K.child-wf NG.≈ˢ-paths
module RTC-T = RTC.Translation NG.C.carrier BG.B
  (λ p → fst (BG.Base.iᴷ p)) (λ p → snd (BG.Base.iᴷ p))
  FB.below BG.Translation.trᴮ CAG.trᴮ-entries-NG TR.trᴾ trᴾ-entries-NG

module FromGeneric (G : Sub) where

  module GL = GI.Laws G using ( generic-forward ; Uof-up )
  module VUV = VU.Value (GI.Uof G)
    using ( _≈[G]_ ; ‖Active‖ ; ≈-intro )

  active-in : (x n b : S) (hb : ⟨ b ∈ˢ BG.B ⟩)
    → ⟨ NG.K.entry x b ∈ˢ n ⟩ → ⟨ GI.Uof G (b , hb) ⟩
    → ⟨ VUV.‖Active‖ x n ⟩
  active-in x n b hb hb∈ hU = ∣ b , hb , hb∈ , hU ∣₁

  active-out : (x n : S) (Q : Ω) → ⟨ VUV.‖Active‖ x n ⟩
    → ((b : S) (hb : ⟨ b ∈ˢ BG.B ⟩) → ⟨ NG.K.entry x b ∈ˢ n ⟩
       → ⟨ GI.Uof G (b , hb) ⟩ → ⟨ Q ⟩)
    → ⟨ Q ⟩
  active-out x n Q h k = PT.rec (snd Q) (λ { (p , hp , hb∈ , hU) → k p hp hb∈ hU }) h

  U-to-below : (b : Pt B) → ⟨ GI.Uof G b ⟩
    → ⟨ ⋁ Cond (λ q → (fst q ∈ˢ FB.below b) ⊓ GI.Uof G (FB.i q)) ⟩
  U-to-below b = PT.map (λ { (p , hp , hp⊩) →
    p , FB.below-in b p (FF.⊩ᴮ-elim p b hp⊩) , GL.generic-forward p hp })

  U-from-below : (b : Pt B) (q : Cond) → ⟨ fst q ∈ˢ FB.below b ⟩
    → ⟨ GI.Uof G (FB.i q) ⟩ → ⟨ GI.Uof G b ⟩
  U-from-below b q hqb huq = GL.Uof-up (FB.i q) b (FB.below-out b q hqb) huq

  module RTV = RTC-T.Value (GI.Uof G)
    VUV._≈[G]_ VUV.‖Active‖ VUV.≈-intro active-in active-out
    U-to-below U-from-below
  module RTN = RTV.Named NG.K.IsName BG.BK.IsName TRV.trᴾ-name
    using ( ext-surjective )

  ext-surjective : (n : S) → ⟨ BG.BK.IsName n ⟩
    → Σ[ τ ∈ NG.K.Name ]
        ⟨ VUV._≈[G]_ (BG.Translation.trᴮ (fst τ)) n ⟩
  ext-surjective = RTN.ext-surjective

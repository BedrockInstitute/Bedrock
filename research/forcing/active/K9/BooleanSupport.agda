{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile

module K9.BooleanSupport
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (families : NameKernel.Families 𝒮)
  (accessible : NameKernel.Accessibility 𝒮)
  (images : NameKernel.MemberImage 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (κ w : ZFStructure.S 𝒮)
  (lem : LEM ℓ)
  where

open import FOL.ZFStructure using ( module hPropStructure )
import Cubical.Induction.WellFounded as WFI
import Cubical.HITs.PropositionalTruncation as PT
import Cubical.Data.Empty as Empty
open import Cubical.Data.Sum using ( inl; inr )
open import Cubical.Functions.Logic using ( ⇔toPath )
import CodedVocabulary
import GroundDescription
import NameSupport
import StandardNames
import TranslateForward
import K4.Algebra
import K4.Atomic
import K4.AtomicLaws
import K4.CheckValues
import K4.ValueSets
import K4.InstanceCoded
import CodedCompletion
import K5.InstanceBase
import K5.Frame
import K9.NameGround
import K9.TranslatedCheck

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open PT using ( ∥_∥₁; ∣_∣₁ )
module NG = K9.NameGround 𝒮 families accessible images pow κ w
  using ( sets; core; hasUnion; hasSeparation; extensional; hasPair; ≈ˢ-paths
        ; module C; module K; module Union; module Check )
open NG using ( sets; core; hasUnion; hasSeparation; extensional; hasPair; ≈ˢ-paths )
module Base = K5.InstanceBase 𝒮 extensional pow hasSeparation ≈ˢ-paths NG.C.presentation NG.C.laws
  using ( codedBase; iᴷ )
module IC = K4.InstanceCoded 𝒮 extensional pow hasSeparation ≈ˢ-paths NG.C.presentation NG.C.laws
  using ( codedLattice; codedComplement; codedComplete; codedNontrivial )
module CO = CodedCompletion.Core 𝒮 extensional pow hasSeparation ≈ˢ-paths NG.C.presentation NG.C.laws
  using ( B )
open K4.Algebra 𝒮 using ( Pt; _≤ᴮ_ )

B : S
B = CO.B

open K4.Algebra.Lattice IC.codedLattice using ( ⊤ᴮ; ⊥ᴮ )
open K4.Algebra.CodedComplete IC.codedComplete
  using ( supᴮ; sup-ub; sup-lub )
private module GD = GroundDescription 𝒮 extensional ≈ˢ-paths using ( ext-path )

module Support (W : S) where
  module K = NameKernel.Kernel 𝒮 core accessible W
    using ( entry; entry-inj; entry-isKPair; singleOf; singleOf-spec; singleOf-member
          ; Child; isPropChild; child-wf; IsName; Shape; name-intro; child-is-name
          ; module RawRec; module RawPairRec )
  module BG = NameSupport.Instantiate.BG 𝒮 sets accessible W
    using ( support; weightsAt; weightsAt-sub; support-in; support-out; support-valid
          ; support-spec; support-bound; weightsAt-spec; support-is-join; kpair-unique )
  open BG public using ( support; weightsAt; weightsAt-sub; support-in; support-out; support-valid )

  entry-in : (n x b : S) → ⟨ b ∈ˢ W ⟩ → ⟨ K.entry x b ∈ˢ n ⟩
    → ⟨ x ∈ˢ support n ⟩
  entry-in n x b hb he = subst ⟨_⟩ (sym (BG.support-spec n x))
    (BG.support-bound n x b he ,
      ∣ K.entry x b , he , ∣ b , hb , K.entry-isKPair x b ∣₁ ∣₁)

  weight-in : (n x b : S) → ⟨ b ∈ˢ W ⟩ → ⟨ K.entry x b ∈ˢ n ⟩
    → ⟨ b ∈ˢ weightsAt n x ⟩
  weight-in n x b hb he = subst ⟨_⟩ (sym (BG.weightsAt-spec n x b))
    (hb , ∣ K.entry x b , he , K.entry-isKPair x b ∣₁)

  weight-out : (n x b : S) → ⟨ b ∈ˢ weightsAt n x ⟩ → ⟨ K.entry x b ∈ˢ n ⟩
  weight-out n x b h = PT.rec (snd (K.entry x b ∈ˢ n))
    (λ { (e , he , pr) → subst (λ z → ⟨ z ∈ˢ n ⟩) (BG.kpair-unique e x b pr) he })
    (snd (subst ⟨_⟩ (BG.weightsAt-spec n x b) h))

  entry-out : (n x : S) → ⟨ x ∈ˢ support n ⟩
    → ∥ Σ[ b ∈ S ] (⟨ b ∈ˢ W ⟩ × ⟨ K.entry x b ∈ˢ n ⟩) ∥₁
  entry-out n x h = PT.map
    (λ { (b , hb) → b , weightsAt-sub n x b hb , weight-out n x b hb })
    (subst ⟨_⟩ (BG.support-is-join n x) h)

module PSupport = Support NG.C.carrier
  using ( support; weightsAt; weightsAt-sub; entry-in; entry-out; weight-in; weight-out; module BG )
module BSupport = Support B
  using ( support; support-in; support-out; weightsAt; weightsAt-sub; entry-in; entry-out; weight-in; weight-out; module K )
module BK = BSupport.K
  using ( entry; entry-inj; entry-isKPair; singleOf; singleOf-spec; singleOf-member
        ; Child; isPropChild; child-wf; IsName; Shape; name-intro; module RawRec; module RawPairRec )

entry-agrees : (x b : S) → BK.entry x b ≡ NG.K.entry x b
entry-agrees x b = PSupport.BG.kpair-unique (BK.entry x b) x b (BK.entry-isKPair x b)

source-entry-in : (n x p : S) → ⟨ p ∈ˢ NG.C.carrier ⟩ → ⟨ BK.entry x p ∈ˢ n ⟩
  → ⟨ x ∈ˢ PSupport.support n ⟩
source-entry-in n x p hp he = PSupport.entry-in n x p hp
  (subst (λ e → ⟨ e ∈ˢ n ⟩) (entry-agrees x p) he)

source-entry-out : (n x : S) → ⟨ x ∈ˢ PSupport.support n ⟩
  → ∥ Σ[ p ∈ S ] (⟨ p ∈ˢ NG.C.carrier ⟩ × ⟨ BK.entry x p ∈ˢ n ⟩) ∥₁
source-entry-out n x h = PT.map
  (λ { (p , hp , he) → p , hp , subst (λ e → ⟨ e ∈ˢ n ⟩) (sym (entry-agrees x p)) he })
  (PSupport.entry-out n x h)

source-weight-in : (n x p : S) → ⟨ p ∈ˢ NG.C.carrier ⟩ → ⟨ BK.entry x p ∈ˢ n ⟩
  → ⟨ p ∈ˢ PSupport.weightsAt n x ⟩
source-weight-in n x p hp he = PSupport.weight-in n x p hp
  (subst (λ e → ⟨ e ∈ˢ n ⟩) (entry-agrees x p) he)

source-weight-out : (n x p : S) → ⟨ p ∈ˢ PSupport.weightsAt n x ⟩ → ⟨ BK.entry x p ∈ˢ n ⟩
source-weight-out n x p h = subst (λ e → ⟨ e ∈ˢ n ⟩) (sym (entry-agrees x p))
  (PSupport.weight-out n x p h)

source-child-name : (n : S) → ⟨ NG.K.IsName n ⟩ → (x : S) → BK.Child x n → ⟨ NG.K.IsName x ⟩
source-child-name n hn x ch = NG.K.child-is-name n hn x
  (PT.map (λ { (p , he) → p , subst (λ e → ⟨ e ∈ˢ n ⟩) (entry-agrees x p) he }) ch)

source-check-spec : (a e : S) → (e ∈ˢ NG.Check.chk a)
  ≡ ⋁ S (λ y → (y ∈ˢ a) ⊓ ⋁ S (λ p → (p ∈ˢ NG.C.carrier)
    ⊓ (e ≈ˢ BK.entry (NG.Check.chk y) p)))
source-check-spec a e = NG.Check.chk-spec a e ∙ cong (⋁ S) (funExt (λ y →
  cong ((y ∈ˢ a) ⊓_) (cong (⋁ S) (funExt (λ p →
    cong (λ z → (p ∈ˢ NG.C.carrier) ⊓ (e ≈ˢ z)) (sym (entry-agrees (NG.Check.chk y) p)))))))

opaque
  weight : S → S → Pt B
  weight n x = supᴮ (BSupport.weightsAt n x) (BSupport.weightsAt-sub n x)

  weight-upper : (n x : S) (b : Pt B) → ⟨ BK.entry x (fst b) ∈ˢ n ⟩
    → ⟨ b ≤ᴮ weight n x ⟩
  weight-upper n x b he = sup-ub (BSupport.weightsAt n x) (BSupport.weightsAt-sub n x)
    b (BSupport.weight-in n x (fst b) (snd b) he)

  weight-least : (n x : S) (v : Pt B)
    → ((b : Pt B) → ⟨ BK.entry x (fst b) ∈ˢ n ⟩ → ⟨ b ≤ᴮ v ⟩)
    → ⟨ weight n x ≤ᴮ v ⟩
  weight-least n x v upper = sup-lub (BSupport.weightsAt n x) (BSupport.weightsAt-sub n x)
    v (λ b hb → upper b (BSupport.weight-out n x (fst b) hb))

private
  module Standard = StandardNames.Kernel 𝒮 BK.entry BK.entry-inj
    BK.singleOf BK.singleOf-spec BK.singleOf-member BK.Child
    (λ x n Q h f → PT.rec (snd Q) (λ { (b , hb) → f b hb }) h)
    ≈ˢ-paths GD.ext-path
    using ( module Validity; module Weighted )
  module Valid = Standard.Validity B BK.Shape (λ n h → h) BK.IsName BK.name-intro
    using ( entries-name )
  module Weighted = Standard.Weighted accessible
    (NameKernel.MemberImage.image images) (NameKernel.MemberImage.image-spec images)
    NG.Union.bigUnion NG.Union.bigUnion-spec
    using ( module Over )

module Checked where
  private
    module OneCheck = Weighted.Over (BK.singleOf (fst ⊤ᴮ))
      using ( chk; chk-spec; module Valid )
    module CheckValid = OneCheck.Valid B BK.IsName Valid.entries-name
      (λ p hp → subst (λ z → ⟨ z ∈ˢ B ⟩) (sym (BK.singleOf-spec (fst ⊤ᴮ) p hp)) (snd ⊤ᴮ))
      using ( chk-name )
  check : S → S
  check = OneCheck.chk

  check-name : (a : S) → ⟨ BK.IsName (check a) ⟩
  check-name = CheckValid.chk-name

  check-spec : (a e : S) → (e ∈ˢ check a)
    ≡ ⋁ S (λ y → (y ∈ˢ a) ⊓ (e ≈ˢ BK.entry (check y) (fst ⊤ᴮ)))
  check-spec a e = OneCheck.chk-spec a e ∙ cong (⋁ S) (funExt (λ y →
    cong ((y ∈ˢ a) ⊓_) (⇔toPath
      {P = ⋁ S (λ p → (p ∈ˢ BK.singleOf (fst ⊤ᴮ)) ⊓ (e ≈ˢ BK.entry (check y) p))}
      {Q = e ≈ˢ BK.entry (check y) (fst ⊤ᴮ)}
      (PT.rec (snd (e ≈ˢ BK.entry (check y) (fst ⊤ᴮ)))
        (λ { (p , hp , eq) → subst (λ z → ⟨ e ≈ˢ BK.entry (check y) z ⟩)
          (BK.singleOf-spec (fst ⊤ᴮ) p hp) eq }))
      (λ eq → ∣ fst ⊤ᴮ , BK.singleOf-member (fst ⊤ᴮ) , eq ∣₁))))

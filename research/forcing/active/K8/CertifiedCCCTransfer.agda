{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile

module K8.CertifiedCCCTransfer
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
    → ZFStructure._≈ˢ_ 𝒮 x y ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  (pair : OrdinaryProfile.Pairing 𝒮)
  (un : OrdinaryProfile.Union 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (sep : OrdinaryProfile.Separation 𝒮)
  (coll : OrdinaryProfile.Collection 𝒮)
  (find : OrdinaryProfile.FoundationInduction 𝒮)
  (seed : ZFStructure.S 𝒮)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import CodedVocabulary 𝒮 using ( subsetΔ; refinesΔ; compatibleΔ )
open import OrdinaryProfile 𝒮 using ( ChoiceSet )
open import GroundDescription 𝒮 ext paths using ( ext-path )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )
import CardinalBridge
import Certificate
import CodedCompletion
import K7.ChainConditions
import K8.GroundSets
import K8.SubsetOrder
import K8.CanonicalCertificate
import K8.CodedCCCTransfer

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

module G = Certificate 𝒮 ext paths
module CB = CardinalBridge 𝒮
module CC = CodedCompletion 𝒮
module CH = K7.ChainConditions 𝒮 ext paths
module GS = K8.GroundSets.Ground 𝒮 ext paths pair un pow sep seed
module SO = K8.SubsetOrder 𝒮 ext paths pair un pow sep seed
module CT = K8.CodedCCCTransfer 𝒮 ext paths pair un pow sep coll find seed
module KC = K8.CanonicalCertificate 𝒮 ext paths pow sep

module OnPresentation (𝔓 : G.Presentation) where
  module P = G.Over 𝔓

  antichain : S → Ω
  antichain d = ⋀ (G.Pt P.carrier) (λ p → (fst p ∈ˢ d) ⇒
    ⋀ (G.Pt P.carrier) (λ q → (fst q ∈ˢ d) ⇒
      (P.compatible p q ⇒ (fst p ≈ˢ fst q))))

  ccc : S → Ω
  ccc w = ⋀ S (λ d → (subsetΔ d P.carrier ⊓ antichain d) ⇒ CB.injectable d w)

  module AtGraph (o : S)
    (reading : (p q : G.Pt P.carrier) → refinesΔ o (fst p) (fst q) ≡ (p P.≼ q))
    where

    compatible-reading : (p q : G.Pt P.carrier)
      → compatibleΔ P.carrier o (fst p) (fst q) ≡ P.compatible p q
    compatible-reading p q = ⇔toPath
      (PT.map (λ { (r , hr , rp , rq) → (r , hr) ,
        subst ⟨_⟩ (reading (r , hr) p) rp , subst ⟨_⟩ (reading (r , hr) q) rq }))
      (PT.map (λ { (r , rp , rq) → fst r , snd r ,
        subst ⟨_⟩ (sym (reading r p)) rp , subst ⟨_⟩ (sym (reading r q)) rq }))

    antichain-reading : (d : S) → antichain d ≡ CH.antichainΔ P.carrier o d
    antichain-reading d = ⇔toPath
      (λ h p hp pd q hq qd comp → h (p , hp) pd (q , hq) qd
        (subst ⟨_⟩ (compatible-reading (p , hp) (q , hq)) comp))
      (λ h p pd q qd comp → h (fst p) (snd p) pd (fst q) (snd q) qd
        (subst ⟨_⟩ (sym (compatible-reading p q)) comp))

    ccc-reading : (w : S) → ccc w ≡ CH.CCC₂ᴵ P.carrier o w
    ccc-reading w = cong (⋀ S) (funExt (λ d →
      cong (_⇒ CB.injectable d w) (cong (subsetΔ d P.carrier ⊓_) (antichain-reading d))))

CCC : S → G.Presentation → Ω
CCC w 𝔓 = OnPresentation.ccc 𝔓 w

module AtPresentation (lem : LEM ℓ) (𝔓 : CC.Presentation)
  (laws : CC.Coded.ForcingLaws 𝔓) (w : S) where

  module P = CC.Coded 𝔓
  module A = KC.AtPresentation 𝔓 laws
  module R = CC.Core ext pow sep paths 𝔓 laws
  module K = CC.Classical ext pow sep paths 𝔓 laws

  certificate : G.Over.CertifiedCompletion A.hostPresentation
  certificate = A.certificate lem

  module N = G.Nonzero A.hostPresentation certificate sep
  module Positive = G.Over N.B⁺
  module Source = OnPresentation.AtGraph A.hostPresentation P.order (λ p q → refl)

  order⁺ : S
  order⁺ = SO.order N.B⁺set

  order-reading : (u v : G.Pt N.B⁺set)
    → refinesΔ order⁺ (fst u) (fst v) ≡ (u Positive.≼ v)
  order-reading u v = ⇔toPath
    (SO.refines-forward N.B⁺set (fst u) (fst v) (snd u) (snd v))
    (SO.refines-backward N.B⁺set (fst u) (fst v) (snd u) (snd v))

  module Target = OnPresentation.AtGraph N.B⁺ order⁺ order-reading

  source-reading : CCC w A.hostPresentation ≡ CH.CCC₂ᴵ P.carrier P.order w
  source-reading = Source.ccc-reading w

  target-reading : CCC w N.B⁺ ≡ CH.CCC₂ᴵ N.B⁺set order⁺ w
  target-reading = Target.ccc-reading w

  module AtChoice (choice : ChoiceSet) where
    module T = CT.AtPresentation choice 𝔓 laws w

    positive-to-nonzero : (u : S) → ⟨ u ∈ˢ T.B⁺set ⟩ → ⟨ u ∈ˢ N.B⁺set ⟩
    positive-to-nonzero u hu = subst ⟨_⟩ (sym (N.B⁺spec u))
      (parts .fst , λ eq → R.positive→nonzero (u , parts .fst) (parts .snd)
        (G.Pt≡ (GS.≈→≡ eq)))
      where
      parts : ⟨ (u ∈ˢ R.B) ⊓ ⋁ S (λ q → q ∈ˢ u) ⟩
      parts = subst ⟨_⟩ (T.B⁺-spec u) hu

    nonzero-to-positive : (u : S) → ⟨ u ∈ˢ N.B⁺set ⟩ → ⟨ u ∈ˢ T.B⁺set ⟩
    nonzero-to-positive u hu = subst ⟨_⟩ (sym (T.B⁺-spec u))
      (parts .fst , K.nonzero→positive lem (u , parts .fst)
        (λ eq → parts .snd (subst ⟨_⟩ (sym (paths u N.botCode)) (cong fst eq))))
      where
      parts : ⟨ (u ∈ˢ R.B) ⊓ ((u ≈ˢ N.botCode) ⇒ ⊥) ⟩
      parts = subst ⟨_⟩ (N.B⁺spec u) hu

    opaque
      positive-carrier-equality : T.B⁺set ≡ N.B⁺set
      positive-carrier-equality = ext-path (λ u →
        ⇔toPath (positive-to-nonzero u) (nonzero-to-positive u))

      positive-order-equality : T.order⁺ ≡ order⁺
      positive-order-equality = cong SO.order positive-carrier-equality

      coded-transfer : ⟨ CH.CCC₂ᴵ P.carrier P.order w ⟩
        → ⟨ CH.CCC₂ᴵ N.B⁺set order⁺ w ⟩
      coded-transfer h = subst (λ B → ⟨ CH.CCC₂ᴵ B (SO.order B) w ⟩)
        positive-carrier-equality (T.transfer h)

      presentation-transfer : ⟨ CCC w A.hostPresentation ⟩ → ⟨ CCC w N.B⁺ ⟩
      presentation-transfer h = subst ⟨_⟩ (sym target-reading)
        (coded-transfer (subst ⟨_⟩ source-reading h))

  record TransferHypotheses : Type ℓ where
    field
      ground-choice : ChoiceSet

  hypotheses-from-choice : ChoiceSet → TransferHypotheses
  hypotheses-from-choice choice = record { ground-choice = choice }

  module Property = G.Property A.hostPresentation certificate sep (CCC w) (CCC w)

  property-transfer : Property.PropertyTransfer
  property-transfer = record
    { hypotheses = TransferHypotheses
    ; transfer = λ h → AtChoice.presentation-transfer (TransferHypotheses.ground-choice h) }

  property-hypotheses-inhabited : ChoiceSet → Property.PropertyTransfer.hypotheses property-transfer
  property-hypotheses-inhabited = hypotheses-from-choice

  certified-ccc-transfer : ChoiceSet → ⟨ CH.CCC₂ᴵ P.carrier P.order w ⟩
    → ⟨ CH.CCC₂ᴵ N.B⁺set order⁺ w ⟩
  certified-ccc-transfer = AtChoice.coded-transfer

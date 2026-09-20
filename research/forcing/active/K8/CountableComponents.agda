{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile

module K8.CountableComponents
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
open import FOL.Syntax using ( Formula; var; con; _∈̇_; ∃̇_ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
open import CodedVocabulary 𝒮 using ( subsetΔ; refinesΔ )
open import K8.FiniteVocabulary 𝒮 using ( finiteIn )
open import OrdinaryProfile 𝒮 using ( ChoiceSet )
import K8.GroundSets
import K8.FinitePairs
import K8.FiniteCountable
import K8.FiniteUnion
import K8.CountableUnion
import K8.CountableZFC
import K8.FamilyImages
import K8.ConnectedComponents
import K8.ComponentStep
import K8.RecursionInduction
import K8.OmegaRecursion
import K8.OmegaSuccessor
import CardinalBridge
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )
module GS = K8.GroundSets.Ground 𝒮 ext paths pair un pow sep seed
module FP = K8.FinitePairs 𝒮 ext paths pair un pow sep seed
module FC = K8.FiniteCountable 𝒮 ext paths pair un pow sep find seed
module FU = K8.FiniteUnion 𝒮 ext paths pair un pow sep seed
module CU = K8.CountableUnion 𝒮 ext paths pair un pow sep coll find seed
module FI = K8.FamilyImages 𝒮 ext paths pair un pow sep coll find seed
module OR = K8.OmegaRecursion 𝒮 ext paths pair un pow sep coll find seed
module OS = K8.OmegaSuccessor 𝒮 ext paths pair un pow sep find seed
module CB = CardinalBridge 𝒮

module Family (lem : LEM ℓ) (choice : ChoiceSet) (w : S) (hw : ⟨ CB.isOmega w ⟩)
  (F X : S) (each : (a : S) → ⟨ a ∈ˢ F ⟩ → ⟨ finiteIn X a ⟩)
  where
  module CC = K8.ConnectedComponents.Family 𝒮 ext paths pair un pow sep coll find seed F X
  module ST = K8.ComponentStep.Family 𝒮 ext paths pair un pow sep coll find seed F X
  module CZ = K8.CountableZFC.AtOmega 𝒮 ext paths pair un pow sep coll find seed lem choice w hw

  module Counted (stars : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ CB.injectable (ST.CS.star x) w ⟩)
    (a : S) (ha : ⟨ a ∈ˢ F ⟩) where

    initial-sub : ⟨ subsetΔ (GS.singleton a) F ⟩
    initial-sub z hz = subst (λ t → ⟨ t ∈ˢ F ⟩)
      (sym (GS.≈→≡ (GS.singleton-witness a .snd z hz))) ha

    initial-in : ⟨ GS.singleton a ∈ˢ ST.Y ⟩
    initial-in = subst ⟨_⟩ (sym (GS.power-spec F (GS.singleton a))) initial-sub

    module RI = K8.RecursionInduction.AtOmega 𝒮 ext paths pair un pow sep coll find seed
      lem w hw ST.Y ST.transition (GS.singleton a) initial-in ST.transition-function ST.transition-total
    module R = RI.R

    orbitFormula : Formula S 2
    orbitFormula = OR.deltaAt (con R.recursion) (var (suc zero)) (var zero)

    orbit : S
    orbit = FI.imageIn w ST.Y orbitFormula

    orbit-out : (A : S) → ⟨ A ∈ˢ orbit ⟩
      → ⟨ ⋁ S (λ n → (n ∈ˢ w) ⊓ CU.Ref R.recursion n A) ⟩
    orbit-out A hA = PT.map (λ { (n , hn , r) → n , hn , OR.coded-ref R.recursion n A r })
      (FI.image-out w ST.Y orbitFormula A hA)

    orbit-in : (n A : S) → ⟨ n ∈ˢ w ⟩ → ⟨ CU.Ref R.recursion n A ⟩ → ⟨ A ∈ˢ orbit ⟩
    orbit-in n A hn r = FI.image-in w ST.Y orbitFormula n A hn
      (R.recursion-typed n A r .snd) (OR.delta-ref R.recursion n A r)

    orbit-countable : ⟨ CB.injectable orbit w ⟩
    orbit-countable = FI.image-countable choice w ST.Y w orbitFormula
      (λ n A B hn hA hB r s → CU.ref-single R.recursion n A B R.recursion-function
        (OR.coded-ref R.recursion n A r) (OR.coded-ref R.recursion n B s))
      (CU.CO.injectable-refl sep coll pair w)

    countFormula : Formula S 1
    countFormula = ∃̇ (CU.injectionFormula w)

    count-reading : (A : S) → ((A ∷ []) ⊨ countFormula) ≡ CB.injectable A w
    count-reading A = cong (⋁ S) (funExt λ f → CU.injection-reading w f A)

    initial-count : ⟨ CB.injectable (GS.singleton a) w ⟩
    initial-count = FC.finite-countable lem w hw F (GS.singleton a) (FP.finite-singleton F a ha)

    count-step : (A B : S) → ⟨ A ∈ˢ ST.Y ⟩ → ⟨ B ∈ˢ ST.Y ⟩
      → ⟨ CU.Ref ST.transition A B ⟩ → ⟨ (A ∷ []) ⊨ countFormula ⟩
      → ⟨ (B ∷ []) ⊨ countFormula ⟩
    count-step A B hA hB r countA = subst ⟨_⟩ (sym (count-reading B))
      (subst (λ t → ⟨ CB.injectable t w ⟩) (sym (ST.transition-next A B r))
        (ST.countable-next lem choice w hw each stars A
          (subst ⟨_⟩ (GS.power-spec F A) hA) (subst ⟨_⟩ (count-reading A) countA)))

    module CI = RI.Invariant countFormula
      (subst ⟨_⟩ (sym (count-reading (GS.singleton a))) initial-count) count-step

    orbit-member-countable : (A : S) → ⟨ A ∈ˢ orbit ⟩ → ⟨ CB.injectable A w ⟩
    orbit-member-countable A hA = PT.rec (snd (CB.injectable A w))
      (λ { (n , hn , r) → subst ⟨_⟩ (count-reading A) (CI.holds n A hn r) }) (orbit-out A hA)

    closure : S
    closure = FU.bigUnion orbit

    closure-countable : ⟨ CB.injectable closure w ⟩
    closure-countable = CZ.countable-bigUnion orbit orbit-countable orbit-member-countable

    closure-sub : ⟨ subsetΔ closure F ⟩
    closure-sub b hb = PT.rec (snd (b ∈ˢ F))
      (λ { (A , hA , bA) → subst ⟨_⟩ (GS.power-spec F A)
        (FI.image-sub w ST.Y orbitFormula A hA) b bA })
      (subst ⟨_⟩ (FU.bigUnion-spec orbit b) hb)

    closure-self : ⟨ a ∈ˢ closure ⟩
    closure-self = subst ⟨_⟩ (sym (FU.bigUnion-spec orbit a))
      ∣ GS.singleton a , orbit-in OS.zeroSet (GS.singleton a) (OS.zero-in w hw) R.recursion-zero
        , GS.singleton-witness a .fst ∣₁

    closure-closed : ⟨ CC.Closed closure ⟩
    closure-closed b hb c hc meet = PT.rec (snd (c ∈ˢ closure))
      (λ { (A , hA , bA) → PT.rec (snd (c ∈ˢ closure))
        (λ { (n , hn , r) → PT.rec (snd (c ∈ˢ closure))
          (λ { (B , hB , s , t) → subst ⟨_⟩ (sym (FU.bigUnion-spec orbit c))
            ∣ B , orbit-in (OS.successor n) B (OS.successor-in w hw n hn) s
              , subst (λ z → ⟨ c ∈ˢ z ⟩) (sym (ST.transition-next A B t))
                (ST.adjacent-next A b c bA hc meet) ∣₁ }) (R.recursion-next n A hn r) })
        (orbit-out A hA) }) (subst ⟨_⟩ (FU.bigUnion-spec orbit b) hb)

    component-countable : ⟨ CB.injectable (CC.component a) w ⟩
    component-countable = CU.CO.injectable-mono-dom (CC.component a) closure w
      (CC.component-least a closure closure-sub closure-self closure-closed) closure-countable

  component-countable : ((x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ CB.injectable (ST.CS.star x) w ⟩)
    → (a : S) → ⟨ a ∈ˢ F ⟩ → ⟨ CB.injectable (CC.component a) w ⟩
  component-countable stars a ha = Counted.component-countable stars a ha

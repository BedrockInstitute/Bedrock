{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile
import CardinalBridge
import K8.OmegaSuccessor

module K7.OrdinalSquare {ℓ}
  (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
    → ZFStructure._≈ˢ_ 𝒮 x y ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  (pair : OrdinaryProfile.Pairing 𝒮) (un : OrdinaryProfile.Union 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮) (sep : OrdinaryProfile.Separation 𝒮)
  (coll : OrdinaryProfile.Collection 𝒮)
  (find : OrdinaryProfile.FoundationInduction 𝒮)
  (seed : ZFStructure.S 𝒮) (lem : LEM ℓ)
  (w : ZFStructure.S 𝒮) (hw : ⟨ CardinalBridge.isOmega 𝒮 w ⟩)
  (d : ZFStructure.S 𝒮) (cd : ⟨ CardinalBridge.isCardinal 𝒮 d ⟩)
  (wd : ⟨ ZFStructure._∈ˢ_ 𝒮 w d ⟩)
  (successor-closed : (a : ZFStructure.S 𝒮) → ⟨ ZFStructure._∈ˢ_ 𝒮 a d ⟩
    → ⟨ ZFStructure._∈ˢ_ 𝒮
      (K8.OmegaSuccessor.successor 𝒮 ext paths pair un pow sep find seed a) d ⟩)
  (members-countable : (a : ZFStructure.S 𝒮) → ⟨ ZFStructure._∈ˢ_ 𝒮 a d ⟩
    → ⟨ CardinalBridge.injectable 𝒮 a w ⟩)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
import Cubical.HITs.PropositionalTruncation as PT
import K7.DiagonalOrderType
import K7.DiagonalRankExistence
import K7.OrdinalDiagonal
import K8.FinitePigeonhole

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )
module Cardinal = CardinalBridge 𝒮
module Types = K7.DiagonalOrderType 𝒮 ext paths pair un pow sep coll find seed lem w hw
  d (cd .fst) successor-closed members-countable
  using ( Rank; rank-unique; initial-ordertype-bound )
module Existence = K7.DiagonalRankExistence 𝒮 ext paths pair un pow sep coll find seed lem w hw
  d (cd .fst) successor-closed members-countable
  using ( rank-exists; rank-injective; rankFormula; rank-reading )
module Diagonal = K7.OrdinalDiagonal.AtOrdinal
  𝒮 ext paths pair un pow sep coll find seed lem w hw d (cd .fst) successor-closed members-countable
  using ( P )
module Graph = K8.FinitePigeonhole.Graph 𝒮 ext paths pair un pow sep coll find seed
  Diagonal.P d Existence.rankFormula
  using ( graph; injection; ref-entry )

rank-bound : (a q : S) → ⟨ Types.Rank a q ⟩ → ⟨ a ∈ˢ d ⟩
rank-bound a q h = PT.rec (snd (a ∈ˢ d))
  (λ { (f , hf) → Types.initial-ordertype-bound q a f (h .fst) cd wd hf }) (h .snd)

squareGraph : S
squareGraph = Graph.graph

square-injection : ⟨ Cardinal.isInjection squareGraph Diagonal.P d ⟩
square-injection = Graph.injection
  (λ q hq → PT.map (λ { (a , h) → a , rank-bound a q h ,
    subst ⟨_⟩ (sym (Existence.rank-reading a q)) h }) (Existence.rank-exists q hq))
  (λ q a b h k → subst ⟨_⟩ (sym (paths a b))
    (Types.rank-unique a b q (subst ⟨_⟩ (Existence.rank-reading a q) h)
      (subst ⟨_⟩ (Existence.rank-reading b q) k)))
  (λ q a z h k → Existence.rank-injective a q z
    (subst ⟨_⟩ (Existence.rank-reading a q) h) (subst ⟨_⟩ (Existence.rank-reading a z) k))

square-bound : ⟨ Cardinal.injectable Diagonal.P d ⟩
square-bound = PT.∣ squareGraph , square-injection ∣₁

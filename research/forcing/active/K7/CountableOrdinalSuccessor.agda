{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile

module K7.CountableOrdinalSuccessor {ℓ}
  (𝒮 : ZFStructure (hPropAlgebra ℓ))
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
  (lem : LEM ℓ)
  (choice : OrdinaryProfile.ChoiceSet 𝒮)
  where

open import FOL.ZFStructure using ( module hPropStructure )
import CardinalBridge
import K7.OrdinalDiagonal
import K7.OrdinalTypeBounds
import K8.GroundSets
import K8.CountableZFC
import K8.FinitePairs
import K8.FiniteCountable
import K8.OmegaSuccessor
import K8.OmegaFinite

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

module Cardinal = CardinalBridge 𝒮 using ( isOmega; isOrdinal; isCardinal; injectable )
module Ground = K8.GroundSets.Ground 𝒮 ext paths pair un pow sep seed
  using ( singleton; singleton-witness )
module Finite = K8.FinitePairs 𝒮 ext paths pair un pow sep seed
  using ( finite-singleton )
module Countable = K8.FiniteCountable 𝒮 ext paths pair un pow sep find seed
  using ( finite-countable )
module Successor = K8.OmegaSuccessor 𝒮 ext paths pair un pow sep find seed
  using ( successor; successor-spec )
module Ordinals = K8.OmegaFinite 𝒮 ext paths pair un pow sep find seed
  using ( successor-ordinal )
module Bounds = K7.OrdinalTypeBounds 𝒮 ext paths sep find lem using ( ordinal-bound )

module AtOmega (w : S) (hw : ⟨ Cardinal.isOmega w ⟩) where

  private
    module Union = K8.CountableZFC.AtOmega 𝒮 ext paths pair un pow sep coll find seed
      lem choice w hw using ( countable-join )
    module Members = K7.OrdinalDiagonal 𝒮 ext paths pair un pow sep coll find seed
      lem w hw using ( ordinal-members )

  singleton-countable : (a : S) → ⟨ Cardinal.injectable (Ground.singleton a) w ⟩
  singleton-countable a = Countable.finite-countable lem w hw
    (Ground.singleton a) (Ground.singleton a)
    (Finite.finite-singleton (Ground.singleton a) a (fst (Ground.singleton-witness a)))

  successor-countable : (a : S) → ⟨ Cardinal.injectable a w ⟩
    → ⟨ Cardinal.injectable (Successor.successor a) w ⟩
  successor-countable a ha = Union.countable-join a (Ground.singleton a)
    ha (singleton-countable a)

  successor-closed : (d : S) → ⟨ Cardinal.isCardinal d ⟩ → ⟨ w ∈ˢ d ⟩
    → ((a : S) → ⟨ a ∈ˢ d ⟩ → ⟨ Cardinal.injectable a w ⟩)
    → (a : S) → ⟨ a ∈ˢ d ⟩ → ⟨ Successor.successor a ∈ˢ d ⟩
  successor-closed d hd wd countable a ha =
    Bounds.ordinal-bound (Successor.successor a) w d
      (Ordinals.successor-ordinal a (Successor.successor a)
        (Members.ordinal-members d (fst hd) a ha) (Successor.successor-spec a))
      hd wd (successor-countable a (countable a ha))

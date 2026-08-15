{-# OPTIONS --cubical --safe --guardedness #-}

-- LJ-1.278 re-run (C-45): imports the new master L.Cardinal and uses each
-- export in a consumer-shaped term, instantiated at the real ordinal ω.
-- A copy that compiles is not a landing; this re-run proves the master
-- is a supply.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-278.ReRun {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Model {ℓ} using ( self∈sucV )
open import V.Presentation {ℓ} using ( fiber )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; Lset→isL )
open import L.Ordinal {ℓ} using ( ω-ord; suc-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.Choice.Step {ℓ} lem using ( Mem )
open import L.Cardinal {ℓ} lem
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( ω; sucV )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )
open hPropStructure 𝒮ʟ using ( S )

-- The real ordinal site: ω is an L-ordinal.
hω : ⟨ isL ω ⟩
hω = Lset→isL (sucV ω) (suc-ord ω-ord) ω (ord∈Lset-suc ω ω-ord)

aω : S
aω = ω , hω

-- A1: the ambient-injection least cardinal at ω, fully instantiated.
module L1 = LeastCardInjL aω ω-ord

selfω : ⟪ sucV (fst aω) ⟫
selfω = fiber (sucV (fst aω)) (self∈sucV (fst aω)) .fst

-- the crossing is inhabited, and carries ω itself
upω : S
upω = L1.up selfω

upω-fst : fst upω ≡ fst aω
upω-fst = fiber (sucV (fst aω)) (self∈sucV (fst aω)) .snd

-- the least cardinal above ω is produced, with its injection and ordinal-ness
κω : S
κω = L1.κ

κω-inj : ∥ ⟪ fst aω ⟫ ↪ ⟪ fst κω ⟫ ∥₁
κω-inj = L1.κ-inj

κω-ord : IsOrd (fst κω)
κω-ord = L1.oκ

-- A3: the canonical selection at ω (outer module; the nonempty witness is
-- A5's deliverable, so `chosen` stays uninstantiated).
module C3 = Canonical aω aω

c3Good : Mem (Lset (SiteBound.β aω)) → Ω
c3Good = C3.Good

-- A4: the internal least cardinal at ω (outer module only), and the two
-- internal predicates used in consumer-shaped types.
module ILC = InternalLeastCard aω ω-ord

ilcGood : Mem (Lset (SiteBound.β aω)) → hProp (ℓ-suc ℓ)
ilcGood = ILC.Good

useCode : S → S → S → Type (ℓ-suc ℓ)
useCode = InjCode

useCard : S → Type (ℓ-suc ℓ)
useCard = IsCardinalL

-- The shared device, used directly.
βω : V ℓ
βω = SiteBound.β aω

oβω : IsOrd βω
oβω = SiteBound.oβ aω

upβω : Mem (Lset βω) → S
upβω = SiteBound.up aω

-- The ambient injection type is importable and usable.
useInj : Type ℓ → Type ℓ → Type ℓ
useInj = _↪_

{-# OPTIONS --cubical --safe --guardedness #-}

-- LJ-1.368 control C.  EXPECTED RED.  It lands nothing.  Repair it never.
--
-- THE PINNING CONTROL for `[LJ-1.365]`'s `statement-fits`
-- (ProbeLJ1365A.agda:95-99) and for `Probe368.agda`'s copy of it.  A
-- hand-spelled conclusion type is worth nothing until a WRONG spelling
-- is measured to fail at the same application.
--
-- The spelling below differs from src/L/GCH.lagda.md:65-68 in ONE
-- conjunct: `InjL (𝒫 κ) δ` becomes a second `InjL δ (𝒫 κ)`.  Everything
-- else is identical.  The delivered statement must refuse it.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-368.MustFail368C {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd )
open import L.Cardinal {ℓ} lem using ( IsCardinalL )
open import L.GCH {ℓ} lem

open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( ω )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )

ConclWrong : (zf : ModelL.isZFModel) (κ : hPropStructure.S 𝒮ʟ)
           → IsOrd (fst κ) → IsCardinalL κ
           → (⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)
           → Type (ℓ-suc ℓ)
ConclWrong zf κ oκ cκ κ∉ω =
  ∥ Σ[ δ ∈ hPropStructure.S 𝒮ʟ ]
       ( SuccCardL δ κ
       × InjL δ (𝒫 κ)
       × InjL δ (𝒫 κ) ) ∥₁
  where open ModelL.isZFModel zf using ( 𝒫 )

-- CONTROL C, SOLO.  The wrong spelling, at the same application.
wrong-fits : (zf : ModelL.isZFModel) (κ : hPropStructure.S 𝒮ʟ)
           → (oκ : IsOrd (fst κ)) (cκ : IsCardinalL κ)
           → (κ∉ω : ⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)
           → GCHStatement zf → ConclWrong zf κ oκ cκ κ∉ω
wrong-fits zf κ oκ cκ κ∉ω st = st κ oκ cκ κ∉ω

{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-280.ReRun {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.ZFModel
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; IsOrd; isL; Lset; Lset→isL )
open import L.Cardinal {ℓ} lem using ( _↪_; IsCardinalL )
open import L.Ordinal {ℓ} using ( ω-ord; suc-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( ω; sucV )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

-- The master under test.
open import L.GCH {ℓ} lem
  using ( SqShape; AbsorbsShape; SuccCardL; GCHStatement )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )
open hPropStructure 𝒮ʟ using ( S )

module ModelL = FOL.ZFModel 𝒮ʟ

-- C-38 guard, re-derived at this site: ω is an L-ordinal, so the κ
-- quantifier of GCHStatement is inhabited at a real site.
module Guard where

  hω : ⟨ isL ω ⟩
  hω = Lset→isL (sucV ω) (suc-ord ω-ord) ω (ord∈Lset-suc ω ω-ord)

  aω : S
  aω = ω , hω

-- The truncated successor-cardinal conclusion, written at the consumer
-- site with the master's SuccCardL.
Concl : ModelL.isZFModel → S → Type (ℓ-suc ℓ)
Concl zf κ =
  ∥ Σ[ δ ∈ S ]
      ( SuccCardL δ κ × (⟪ fst (ModelL.isZFModel.𝒫 zf κ) ⟫ ↪ ⟪ fst δ ⟫) ) ∥₁

-- A proof of GCHStatement zf, when it exists, is a function of the two
-- hypotheses and a cardinal.  This term applies such a proof at the
-- consumer site: given the two hypotheses and the cardinal, it returns
-- exactly Concl.
apply : (zf : ModelL.isZFModel) (proof : GCHStatement zf)
        (sq : SqShape) (absorbs : AbsorbsShape) (κ : S)
        (cκ : IsCardinalL κ) (nfin : ⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)
      → Concl zf κ
apply zf proof sq absorbs κ cκ nfin = proof sq absorbs κ cκ nfin

-- The two hypotheses stay unsupplied: a proof of GCHStatement zf needs
-- SqShape and AbsorbsShape as inputs, which this site does not build.
-- (Their types are the ones the master names; nothing here inhabits them.)

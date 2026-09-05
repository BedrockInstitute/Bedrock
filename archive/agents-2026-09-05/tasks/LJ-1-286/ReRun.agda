{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.286] the landing proof (C-45).  Exit 0 of a master is not a supply.
-- This file IMPORTS the edited src/L/GCH.lagda.md and uses what it exports.
--
-- PART 1  THE PARAMETER IS GONE.  `apply` takes a proof of `GCHStatement zf`
--         and feeds it `sq` and then the CARDINAL.  If the master still
--         carried `(absorbs : AbsorbsShape) →`, `proof sq κ` would be
--         ill-typed and this file would be red.  So the type of the
--         application is the evidence, not a reading of the source.
-- PART 2  THE SUPPLY IS REAL.  `L.GCH.absorbsL` is exported and has type
--         `AbsorbsShape`.  C-38: the discharge is an inhabitant, never a
--         deletion.
-- PART 3  THE SUPPLY IS NOT VACUOUS.  `absorbsL` is applied at a REAL
--         L-ordinal, ω, and it returns a real ambient injection
--         `⟪ sucV ω ⟫ ↪ ⟪ ω ⟫` whose function and whose injectivity both
--         come out.  A hypothesis whose type nothing can satisfy would stop
--         here.
--
-- This file also carries the C-38 site guard that
-- agents/tasks/LJ-1-280/ReRun.agda:38-44 carried, because that file is a
-- consumer this change breaks (report section 6) and it is outside this
-- task's write territory.
--
-- Tracked; ONE agda process under GHCRTS="-A64m -I0 -M8g".

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-286.ReRun {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.ZFModel
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; IsOrd; isL; Lset; Lset→isL )
open import L.Cardinal {ℓ} lem using ( _↪_; IsCardinalL )
open import L.Ordinal {ℓ} using ( ω-ord; suc-ord; #∈ω )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.Axioms.Infinity {ℓ} lem using ( ωʟ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( ω; sucV; #_ )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

-- The master under test.
open import L.GCH {ℓ} lem
  using ( SqShape; AbsorbsShape; SuccCardL; GCHStatement; absorbsL )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )
open hPropStructure 𝒮ʟ using ( S )

module ModelL = FOL.ZFModel 𝒮ʟ

-- ---------------------------------------------------------------------
-- The C-38 site guard: ω is an L-ordinal, so the κ quantifier of
-- GCHStatement is inhabited at a real site.
-- ---------------------------------------------------------------------

module Guard where

  hω : ⟨ isL ω ⟩
  hω = Lset→isL (sucV ω) (suc-ord ω-ord) ω (ord∈Lset-suc ω ω-ord)

  aω : S
  aω = ω , hω

-- ---------------------------------------------------------------------
-- PART 1.  THE STATEMENT NO LONGER CARRIES THE `absorbs` PARAMETER.
-- ---------------------------------------------------------------------

Concl : ModelL.isZFModel → S → Type (ℓ-suc ℓ)
Concl zf κ =
  ∥ Σ[ δ ∈ S ]
      ( SuccCardL δ κ × (⟪ fst (ModelL.isZFModel.𝒫 zf κ) ⟫ ↪ ⟪ fst δ ⟫) ) ∥₁

-- ONE hypothesis, then the cardinal.  `proof sq κ` is the whole test: with
-- the deleted parameter still in place, κ would land in the `absorbs` slot
-- and this line would be red.
apply : (zf : ModelL.isZFModel) (proof : GCHStatement zf)
        (sq : SqShape) (κ : S)
        (cκ : IsCardinalL κ) (nfin : ⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)
      → Concl zf κ
apply zf proof sq κ cκ nfin = proof sq κ cκ nfin

-- ---------------------------------------------------------------------
-- PART 2.  THE MASTER SUPPLIES A6's SHAPE.
-- ---------------------------------------------------------------------

supplied : AbsorbsShape
supplied = absorbsL

-- ---------------------------------------------------------------------
-- PART 3.  THE SUPPLY RUNS AT A REAL L-ORDINAL.  Not vacuous.
-- ---------------------------------------------------------------------

module Live where

  -- ω is an L-ordinal, it is not a member of ω, and it holds every
  -- numeral.  Those are exactly `AbsorbsShape`'s three hypotheses.
  atω : ⟪ sucV (fst ωʟ) ⟫ ↪ ⟪ fst ωʟ ⟫
  atω = absorbsL ωʟ ω-ord (∈-irrefl ω) (λ k → #∈ω k)

  -- The injection's two halves both come out.
  theFun : ⟪ sucV ω ⟫ → ⟪ ω ⟫
  theFun = fst atω

  theInj : (x y : ⟪ sucV ω ⟫) → theFun x ≡ theFun y → x ≡ y
  theInj = snd atω

-- ---------------------------------------------------------------------
-- `SqShape` STAYS UNSUPPLIED.  Nothing here inhabits it, and nothing in
-- src/ does either (report section 5).  The statement still takes it.
-- ---------------------------------------------------------------------

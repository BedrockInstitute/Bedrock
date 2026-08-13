{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.121] probe A: levelIn and cover at the site.  Refutation
-- attempt first, then the supply wall.
--
-- The two hypotheses (src/L/BoundedSubset.lagda.md:1409-1411) are the
-- two halves of Devlin 5.2 part (i), the condensation level-hood
-- transfer.  This probe restates them at the [LJ-1.94] site (alpha =
-- omega, x = empty, kappa = Hartogs), attempts the ProbeLJ197A-style
-- refutation, and shows the supply reduces to the one fact the tree
-- does not deliver: the hull is closed under the level construction at
-- the ordinals it contains.
--
-- Untracked probe; ONE agda process under GHCRTS="-A64m -I0 -M8g";
-- never committed.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ1121A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import L.Constructible {ℓ} using ( IsOrd; Lset )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
import L.BoundedSubset {ℓ} lem as BS
open BS using ( _↪_ )
import ProbeLJ1119A {ℓ} lem as P119
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

module BA = P119.BA

-- =====================================================================
-- THE TWO TARGETS, RESTATED AT THE SITE.  These are exactly the types
-- of the first hypotheses nothing supplies (BoundedSubset.lagda.md:
-- 1409-1411), instantiated at the [LJ-1.94] site values.
-- =====================================================================

LevelIn : Type (ℓ-suc ℓ)
LevelIn = (δ : S) → IsOrd δ → ⟨ δ ∈ˢ BA.HS.C.πX ⟩ → ⟨ Lset δ ∈ˢ BA.HS.C.πX ⟩

Cover : Type (ℓ-suc ℓ)
Cover = (y : S) → ⟨ y ∈ˢ BA.HS.M ⟩
      → ∥ Σ[ γ ∈ S ] (IsOrd γ × ⟨ γ ∈ˢ BA.HS.C.πX ⟩ × ⟨ BA.HS.C.π y ∈ˢ Lset γ ⟩) ∥₁

-- =====================================================================
-- REFUTATION ATTEMPT.  ProbeLJ197A refutes by varying a FRAME: it picks
-- a frame where the universally quantified set is unconstrained and
-- derives a membership cycle.  That shape does not apply here.  There
-- is no frame to vary: the site's hull carrier BA.HS.M and its collapse
-- image BA.HS.C.πX are FIXED, and both statements are guarded by real
-- premises (IsOrd delta, delta in piX; y in M).  A refutation would be
-- a counterexample: a specific ordinal delta of the collapse whose
-- level leaves the collapse, or a hull member whose collapse value
-- escapes every level below the collapse's ordinals.  Both would
-- contradict Devlin 5.2 part (i): the collapse of the definable hull is
-- a level, so it is closed under the level construction at its own
-- ordinals and every collapsed member lies in a level below the
-- collapse's ordinals.  No delivered regularity lemma (∈-irrefl, the
-- no-cycle lemmas) fires on a positive, premise-guarded membership
-- about a SPECIFIC set, so there is no term of the refutation type
-- below.
-- =====================================================================

-- The refutation types: if either were empty, one of these would be
-- inhabited.  This probe found no term for either.
RefuteLevelIn : Type (ℓ-suc ℓ)
RefuteLevelIn = LevelIn → Empty.⊥

RefuteCover : Type (ℓ-suc ℓ)
RefuteCover = Cover → Empty.⊥

-- =====================================================================
-- THE SUPPLY WALL.  levelIn reduces to two facts, and both are the
-- level-hood transfer (the [LJ-1.12] crossing).  The first is the
-- hull's closure under the level construction:
--   hullLevel : (delta : S) -> IsOrd delta -> < delta in piX >
--             -> < Lset delta in M >
-- The second is the collapse fixing the level:
--   piFixesLevel : (delta : S) -> IsOrd delta -> < delta in piX >
--                -> C.pi (Lset delta) ≡ Lset delta
-- Both are the transfer of the internalized level-hood statement into
-- the hull (devlin-II5.md section 2.3 Step C); neither is delivered by
-- any master (the grep in the report is the evidence).  cover needs the
-- same transfer in the covering direction (devlin-II5.md section 1.2,
-- the (j) line): every hull member's collapse value lies below an
-- ordinal level of the collapse.
--
-- The module below states the reduction shape: GIVEN the transfer, the
-- two hypotheses close at the site.  The parameters are the two facts
-- the tree does not supply; they are stated here as parameters to name
-- the wall, not added to any master (the brief forbids adding them to
-- the site, and a probe may state the missing term to show the wall).
-- =====================================================================

module Supply
  (hullLevel : (δ : S) → IsOrd δ → ⟨ δ ∈ˢ BA.HS.C.πX ⟩ → ⟨ Lset δ ∈ˢ BA.HS.M ⟩)
  (piFixesLevel : (δ : S) → IsOrd δ → ⟨ δ ∈ˢ BA.HS.C.πX ⟩ → BA.HS.C.π (Lset δ) ≡ Lset δ)
  where

  levelIn : LevelIn
  levelIn δ oδ δ∈πX = subst (λ w → ⟨ w ∈ˢ BA.HS.C.πX ⟩)
    (piFixesLevel δ oδ δ∈πX)
    (BA.HS.C.πX-intro (Lset δ) (hullLevel δ oδ δ∈πX))

-- cover reduces to the covering transfer.  It is stated here only as a
-- type, to name the wall; writing it needs the (j)-line transfer, the
-- same crossing as hullLevel, in the covering direction.

CoverTransfer : Type (ℓ-suc ℓ)
CoverTransfer = (y : S) → ⟨ y ∈ˢ BA.HS.M ⟩
              → ∥ Σ[ γ ∈ S ] (IsOrd γ × ⟨ γ ∈ˢ BA.HS.C.πX ⟩ × ⟨ BA.HS.C.π y ∈ˢ Lset γ ⟩) ∥₁

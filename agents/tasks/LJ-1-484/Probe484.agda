{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.484] PROBE.  cover, first obligation of this hypothesis.
-- It runs in agents/tasks/LJ-1-484/ and lands nothing in src/.
--
--   STEP ONE, W3 FIRST  code-of, obligation omitted.
--                       Hull membership IS a truncated code.
--                       Site: src/L/Hull.lagda.md:337-339.
--
--   STEP TWO            D-10 types. See review-of-cover.md.
--                       No term named cover.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-484.Probe484 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; Lset; Lset-out; 𝒟ₒ )
open import L.Axioms.Basic {ℓ} using ( Lset-suc )
open import L.Ordinal {ℓ} using ( suc-ord; mem-ord )
open import L.Hull {ℓ} lem using ( module AtStage )
open import V.Collapse {ℓ} using ( module Collapse )

open import Cubical.Data.Sigma using ( Σ-syntax )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ ; map )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; module InfinitySet )
open InfinitySet using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- Telescope copied from src/L/BoundedSubset.lagda.md:903-914.
-- The brief names :903-916. Line :916 is module Condense.
-- Nothing below module Condense is copied. levelIn is not a hypothesis.

module HullStage (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : S) (X⊆L : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  module ASt = AtStage lam ordλ

  module H = ASt.Hull X X⊆L ∅∈λ

  M : S
  M = H.T.Hull

  module C = Collapse M

  open H.T using ( Code; val )

  -- =====================================================================
  -- W3.  code-of.  Obligation omitted.
  -- =====================================================================

  -- Hull membership is definitionally a truncated code.
  -- Site: src/L/Hull.lagda.md:337-339, hull-member x x∈H = x∈H.
  -- Hull itself: src/L/Hull.lagda.md:113-115, sett Code (λ c → toSet (val c)).

  code-of : (y : S) → ⟨ y ∈ˢ M ⟩ → ∥ Σ[ c ∈ Code ] (fst (val c) ≡ y) ∥₁
  code-of = H.hull-member

  -- =====================================================================
  -- D-10 STEPS AS TYPES.  Steps 1, 3, 5, 6 delivered. Steps 2, 4, 7
  -- unbuilt. The obligation is omitted. No term named cover.
  -- =====================================================================

  -- Step 3. Ambient covering at the stage. Delivered. The index is a
  -- member of lam, not of M. Site: src/L/Constructible.lagda.md:336-337
  -- with Hull⊆L at src/L/Hull.lagda.md:330-331.

  ambient-cover : (y : S) → ⟨ y ∈ˢ M ⟩
                → ∥ Σ[ δ ∈ S ] (⟨ δ ∈ˢ lam ⟩ × ⟨ y ∈ˢ 𝒟ₒ (Lset δ) ⟩) ∥₁
  ambient-cover y y∈M = Lset-out lam y (H.Hull⊆L y y∈M)

  -- Same covering, renamed to a level. Still the index is in lam.
  -- Lset-suc at src/L/Axioms/Basic.lagda.md:196. suc-ord and mem-ord
  -- at src/L/Ordinal.lagda.md:96 and :221. succλ is the telescope.

  ambient-level : (y : S) → ⟨ y ∈ˢ M ⟩
                → ∥ Σ[ γ ∈ S ] (IsOrd γ × ⟨ γ ∈ˢ lam ⟩ × ⟨ y ∈ˢ Lset γ ⟩) ∥₁
  ambient-level y y∈M = PT.map go (ambient-cover y y∈M)
    where
    go : Σ[ δ ∈ S ] (⟨ δ ∈ˢ lam ⟩ × ⟨ y ∈ˢ 𝒟ₒ (Lset δ) ⟩)
       → Σ[ γ ∈ S ] (IsOrd γ × ⟨ γ ∈ˢ lam ⟩ × ⟨ y ∈ˢ Lset γ ⟩)
    go (δ , δ∈λ , y∈𝒟) =
      sucV δ
      , ( suc-ord (mem-ord {A = lam} ordλ δ δ∈λ)
        , succλ δ δ∈λ
        , subst (λ w → ⟨ y ∈ˢ w ⟩) (sym (Lset-suc δ)) y∈𝒟 )

  -- The code does not supply that bound. Diagnostic: the covering of
  -- a code value is still ambient-cover, not a read of wit's formula.

  code-ambient : (c : Code)
               → ∥ Σ[ δ ∈ S ] (⟨ δ ∈ˢ lam ⟩ × ⟨ fst (val c) ∈ˢ 𝒟ₒ (Lset δ) ⟩) ∥₁
  code-ambient c = ambient-cover (fst (val c)) (H.val-in-Hull c)

  -- Step 2, the brief's first cut. WRONG SHAPE. A Code does not
  -- carry an ordinal. Unbuilt. Not a supplier of cover.

  StageBoundOfCode : Type (ℓ-suc ℓ)
  StageBoundOfCode =
    (c : Code) → Σ[ γ ∈ S ] (IsOrd γ × ⟨ fst (val c) ∈ˢ Lset γ ⟩)

  -- Step 4. Witnesses inside the hull. Unbuilt. Devlin's Σ₁ transfer
  -- of "∃γ∃v∃z(φ(z,v,γ) ∧ x ∈ v)" (dev/literature/devlin-II5.md:107-108).
  -- Needs the index IN M. Ambient covering does not give that, because
  -- the hull is not transitive (agents/tasks/LJ-1-160/lj-1.160-report.md:248).
  -- The tree's Φ is LsetGraphAt, Formula CS.S n, at
  -- src/L/Coding/Sequence.lagda.md:349. wit takes Formula (⊥* {ℓ}) (suc k)
  -- at src/L/Hull.lagda.md:74. Those types do not meet. [LJ-1.462]
  -- measured that meeting. This probe does not re-run it.

  CoverWitnessesInHull : Type (ℓ-suc ℓ)
  CoverWitnessesInHull =
    (y : S) → ⟨ y ∈ˢ M ⟩
    → ∥ Σ[ γ ∈ S ] (⟨ γ ∈ˢ M ⟩ × IsOrd γ × ⟨ y ∈ˢ Lset γ ⟩) ∥₁

  -- Step 5. Membership along the collapse, both ends in M. Delivered.
  -- Site: src/V/Collapse.lagda.md:102-103.

  π-mem : (x y : S) → y ∈ᵗ x → y ∈ᵗ M → ⟨ C.π y ∈ˢ C.π x ⟩
  π-mem = C.π∈-fwd

  -- Step 6. The index in the image, when the preimage is in M.
  -- Delivered. Site: src/V/Collapse.lagda.md:86-87.

  index-in-image : (γ : S) → ⟨ γ ∈ˢ M ⟩ → ⟨ C.π γ ∈ˢ C.πX ⟩
  index-in-image = C.πX-intro

  -- Step 7. Decode at the image. Unbuilt. Devlin identifies the
  -- covering value by Φ and Σ₀ absoluteness at the transitive
  -- collapse image. It does not commute π with Lset. levelIn is
  -- not a hypothesis.

  CoveredAtImage : Type (ℓ-suc ℓ)
  CoveredAtImage =
    (y : S) → ⟨ y ∈ˢ M ⟩
    → ∥ Σ[ γ ∈ S ] (⟨ γ ∈ˢ M ⟩ × IsOrd (C.π γ)
                  × ⟨ C.π y ∈ˢ Lset (C.π γ) ⟩) ∥₁

  -- The consumer's obligation. UNBUILT. Not a term named cover.

  Cover : Type (ℓ-suc ℓ)
  Cover =
    (y : S) → ⟨ y ∈ˢ M ⟩
    → ∥ Σ[ γ ∈ S ] (IsOrd γ × ⟨ γ ∈ˢ C.πX ⟩ × ⟨ C.π y ∈ˢ Lset γ ⟩) ∥₁


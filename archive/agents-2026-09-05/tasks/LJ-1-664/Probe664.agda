{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.664] PROBE.  Is the hull closed under the definable powerset.
-- It runs in agents/tasks/LJ-1-664/ and lands nothing in src/.
--
-- THE OBLIGATION the brief names is DeeInHull, the type [LJ-1.652]
-- printed (Probe652.agda:280-281).  This file does NOT inhabit that
-- type as a closed term.  It records the search: the consumer is ten
-- lines from a code map (imported, not rewritten), the SM code map the
-- brief priced is already in src/, and two unpaid suppliers remain.
--
-- Nothing is postulated.  Nothing is holed.  Nothing lands in src/.
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M2g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-664.Probe664 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Manipulation.Parameters using ( countFo )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; Lset; 𝒟ₒ )
open import L.Ordinal.StageArith {ℓ} lem using ( sucIter )
open import L.Coding.Graph {ℓ} lem using ( satGraphAt )
open import L.Coding.Powerset {ℓ} lem using ( DefAt )
open import L.Axioms.Separation {ℓ} lem using ( mkBoundedFo; Below′ )
open import FOL.Manipulation.Bounding using ( BoundedFo )
open import LJ-1-647.Probe647 {ℓ} lem using ( module HullStage )

open import Cubical.Data.Unit using ( Unit*; tt* )
open import Cubical.Data.Sigma using ( Σ-syntax )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; module InfinitySet )
open InfinitySet using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- =====================================================================
-- W3.  THE CENSUS OF THE ONLY DELIVERED 𝒟ₒ-FORMULA.
--
-- countFo counts `con` occurrences and nothing else
-- (src/FOL/Manipulation/Parameters.lagda.md:70-86).  The seal at
-- src/L/Coding/Graph.lagda.md:203 stops the count, so it is opened
-- here; opening it is legal in a probe and costs nothing in src/.
--
-- [LJ-1.651]'s lset-formula has countFo ≡ 0 (Probe651.agda:115-116).
-- DefAt, the object-language description of 𝒟ₒ
-- (src/L/Coding/Powerset.lagda.md:442-443), does not.  The cheap Σ₀
-- route that closed the Lset analogue has no delivered twin for 𝒟ₒ.
-- =====================================================================

opaque
  unfolding satGraphAt

  census-DefAt : {n : ℕ} (u w : Fin n) → countFo (DefAt u w) ≡ 166
  census-DefAt u w = refl

  -- [LJ-1.514]'s instrument, re-measured at DefAt.  The 166 constants
  -- all lie in some stage: mkBoundedFo is total
  -- (src/L/Axioms/Separation.lagda.md:449).  That transports DefAt to
  -- a STAGE alphabet.  It does not produce a Formula Code.
  defAt-bound : {n : ℕ} (u w : Fin n)
              → Σ[ σ ∈ V ℓ ] (IsOrd σ × BoundedFo (Below′ σ) (DefAt u w))
  defAt-bound u w = mkBoundedFo (DefAt u w)

-- =====================================================================
-- THE TELESCOPE.  [LJ-1.647]'s HullStage, which is [LJ-1.462]'s minus
-- `module C = Collapse M`.  DeeInHull names no π, so the cut is the
-- right one.  The generic consumer hull-closed-op∥ lives in that
-- module and is not rewritten (W2).
-- =====================================================================

module At (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : S) (X⊆L : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  module HS = HullStage lam ordλ succλ X X⊆L ∅∈λ

  M : S
  M = HS.M

  open HS.H.T using ( Code; val )
  open HS using ( hull-closed-op∥ )

  -- THE STRUCTURAL FACT, imported as hull-mem-is-code in [LJ-1.647]
  -- (Probe647.agda:89-91): to be in the hull IS to be the value of a
  -- code, definitionally.
  hull-mem-is-code : (x : S)
                   → ⟨ x ∈ˢ M ⟩ ≡ ∥ Σ[ c ∈ Code ] (fst (val c) ≡ x) ∥₁
  hull-mem-is-code x = refl

  -- ===================================================================
  -- THE OPERATION CODE MAP, THE OBJECT THE CONSUMER SPENDS.
  -- Truncated, because the goal ⟨ 𝒟ₒ y ∈ˢ M ⟩ is an hProp and
  -- hull-closed-op∥ already takes the truncated form
  -- (Probe647.agda:135-148).  No IsOrd side condition: 𝒟ₒ applies to
  -- any set.
  -- ===================================================================

  DeeCode∥ : Type (ℓ-suc ℓ)
  DeeCode∥ =
    (c : Code) → ∥ Σ[ d ∈ Code ] (fst (val d) ≡ 𝒟ₒ (fst (val c))) ∥₁

  -- THE CONSUMER.  W2: one instance of hull-closed-op∥, not a second
  -- proof.  This is [LJ-1.647]'s ten-line fact at F = 𝒟ₒ and P = Unit*.
  -- IT IS NOT THE OBLIGATION: the obligation has no DeeCode∥ argument.
  dee-from-code : DeeCode∥
                → (y : S) → ⟨ y ∈ˢ M ⟩ → ⟨ 𝒟ₒ y ∈ˢ M ⟩
  dee-from-code dc y y∈M =
    hull-closed-op∥ 𝒟ₒ (λ _ → Unit*) (λ c _ → dc c) y y∈M tt*

  -- The brief's type, named here so the search can point at it, and
  -- NOT lifted to the probe module.  The witness meter reads
  -- Target.DeeInHull at the probe module (scripts/pod/witness.py:278).
  -- Leaving the name inside At is the stated NO-GO: the closed term
  -- the brief asked for is not built.
  DeeInHull : Type (ℓ-suc ℓ)
  DeeInHull = (y : S) → ⟨ y ∈ˢ M ⟩ → ⟨ 𝒟ₒ y ∈ˢ M ⟩

  -- THE TOWER FACT [LJ-1.652] priced and did not build
  -- (lj-1.652-report.md:375-380).  Named, not inhabited.  The tree's
  -- own statement of it is Bound.PowIter's hypothesis
  -- (src/L/Coding/Bound.lagda.md:151-152), which has no supplier.
  -- Verbatim the tree's unpaid hypothesis
  -- (src/L/Coding/Bound.lagda.md:151-152).  Named, not inhabited.
  PowIter : Type (ℓ-suc ℓ)
  PowIter = (δ y : S) → ⟨ y ∈ˢ Lset δ ⟩
          → ∥ Σ[ k ∈ ℕ ] ⟨ 𝒟ₒ y ∈ˢ Lset (sucIter k δ) ⟩ ∥₁

-- DeeInHull is not lifted.  The witness meter reads Target.DeeInHull
-- at this module (scripts/pod/witness.py:278) and will not find it.

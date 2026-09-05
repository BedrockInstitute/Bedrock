{-# OPTIONS --cubical --safe --guardedness #-}

-- LJ-1.170 probe A.  Price the two arms of `[LJ-1.169]`'s fork.
--
-- CRITERIA, FIXED IN WRITING BEFORE THE FIRST `agda` INVOCATION (D-1):
--   wall clock  10 minutes per agda invocation, GHCRTS="-A64m -I0 -M8g",
--               ONE process, cap NEVER raised.  A wall is reported with
--               its wall-clock and the task STOPS.
--   the target  GO if the Devlin-split key lands at a FIXED finite
--               iterate above the carrier, uniformly in the formula and
--               in the number of parameters, at or below 60 in-fence
--               lines.  NO-GO if the bound needs the formula's depth,
--               or above 60 lines.
--   counting    non-blank, non-comment lines, the convention
--               `[LJ-1.167]` re-derived and `[LJ-1.169]` re-used.
--
-- WHAT THIS FILE MEASURES.
--
--   `[LJ-1.169]` MEASURED that this tree's code carries the carrier's
--   members at the LEAVES of a nested Kuratowski tree, so the stage a
--   code needs grows as `2 * depth`
--   (`agents/tasks/LJ-1-169/lj-1.169-report.md:236-253`).  Devlin's
--   `K(u)` instead holds finite SEQUENCES over a FIXED formula set, so
--   his parameters cost ONE uniform bump
--   (`_build/literature/dev2.txt:600-608`).
--
--   THE MEASUREMENT: this tree ALREADY HAS Devlin's split.  It is
--   `nameOf φ = countFo φ , (absFo φ , constantsFo φ)`
--   (`src/L/Choice/Name.lagda.md:381`), delivered and green on the AC
--   side.  BLOCK 1 puts that triple's key at a FIXED iterate.  Nothing
--   in `src/FOL/Coding.lagda.md` is touched, and `⌜_⌝` keeps its nested
--   shape, because the nesting is FREE once the formula is
--   parameter-free (`code∈limit`, `src/L/Choice/Name.lagda.md:153`).
--
-- P-i [F] is obeyed: every implicit set index at a concrete argument is
-- written out.
--
-- No master is edited.  This file is a probe and lives beside the
-- report, per D-1 and `AGENTS.md`.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-170.ProbeLJ1170A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import FOL.Manipulation.Relabelling using ( embed )
open import FOL.Manipulation.Parameters using ( countFo; constantsFo; absFo )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; module VCode )
open import V.Model {ℓ} using ( ∈sucV-inl )
open import L.Constructible {ℓ} using ( IsOrd; Lset; 𝒟ₒ; Lset-mono )
open import L.Axioms.Basic {ℓ}
  using ( Lset-suc; pr∈Lset-suc; finSet; module FinOf )
open import L.Choice.Name {ℓ} lem using ( numeral∈limit; code∈limit )
open import L.Ordinal.StageArith {ℓ} lem using ( sucIter; +ω; +ω-iter )

open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Data.Vec using ( lookup )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( #_; ω; sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- =====================================================================
-- BLOCK 1: THE DEVLIN-SPLIT KEY LANDS AT A FIXED ITERATE.
--
-- A split key is the arity, the code of the PARAMETER-FREE formula, and
-- the parameter vector as a set.  Each of the three has a bound that
-- does NOT mention the formula's depth:
--   the arity numeral    `Lset ω`, `numeral∈limit`
--   the code             `Lset ω`, `code∈limit`  <- the whole point
--   the parameter set    `Lset (sucV σ)`, `finSet∈𝒟ₒ` and `Lset-suc`
-- Two `pr` applications then cost FOUR stages, by `pr∈Lset-suc`.
-- =====================================================================

-- The parameter vector, read as a set at the carrier.
paramSet : (σ : S) (k : ℕ) (g : Fin k → ⟪ Lset σ ⟫) → S
paramSet σ k g = finSet k (λ i → ⟪ Lset σ ⟫↪ (g i))

-- One stage, whatever `k` is.  This is Devlin's `Pow`/`Seq` bump and
-- the tree has had it since `src/L/Axioms/Basic.lagda.md:352-354`.
paramSet∈ : (σ : S) (oσ : IsOrd σ) (k : ℕ) (g : Fin k → ⟪ Lset σ ⟫)
          → ⟨ paramSet σ k g ∈ˢ Lset (sucV σ) ⟩
paramSet∈ σ oσ k g =
  subst (λ w → ⟨ paramSet σ k g ∈ˢ w ⟩) (sym (Lset-suc σ))
    (FinOf.finSet∈𝒟ₒ σ oσ k g)

-- A member of `Lset ω` sits in every stage above `σ` once `ω ∈ σ`.
fromω : (σ : S) → ⟨ ω ∈ˢ σ ⟩ → (d : ℕ) (x : S)
      → ⟨ x ∈ˢ Lset ω ⟩ → ⟨ x ∈ˢ Lset (sucIter (suc d) σ) ⟩
fromω σ ω∈ zero    x h = Lset-mono {α = sucV σ} {β = ω} (∈sucV-inl ω∈) {x = x} h
fromω σ ω∈ (suc d) x h =
  Lset-mono {α = sucIter (suc (suc d)) σ} {β = ω}
    (∈sucV-inl (fromω' d)) {x = x} h
  where
  fromω' : (e : ℕ) → ⟨ ω ∈ˢ sucIter (suc e) σ ⟩
  fromω' zero    = ∈sucV-inl ω∈
  fromω' (suc e) = ∈sucV-inl (fromω' e)

-- THE KEY, and THE MEASUREMENT.  `χ` is parameter-free, `g` is the
-- parameter vector, and the bound mentions NEITHER the depth of `χ` nor
-- the length `k`.
splitKey : (σ : S) (n k : ℕ) (χ : Formula (⊥* {ℓ}) (n + k))
           (g : Fin k → ⟪ Lset σ ⟫) → S
splitKey σ n k χ g = pr (# n) (pr VCode.⌜ embed χ ⌝ (paramSet σ k g))

splitKey∈ : (σ : S) (oσ : IsOrd σ) (ω∈ : ⟨ ω ∈ˢ σ ⟩) (n k : ℕ)
            (χ : Formula (⊥* {ℓ}) (n + k)) (g : Fin k → ⟪ Lset σ ⟫)
          → ⟨ splitKey σ n k χ g ∈ˢ Lset (sucIter 5 σ) ⟩
splitKey∈ σ oσ ω∈ n k χ g =
  pr∈Lset-suc (sucIter 3 σ) (# n) (pr VCode.⌜ embed χ ⌝ (paramSet σ k g))
    (fromω σ ω∈ 2 (# n) (numeral∈limit n))
    (pr∈Lset-suc (sucV σ) VCode.⌜ embed χ ⌝ (paramSet σ k g)
      (fromω σ ω∈ 0 VCode.⌜ embed χ ⌝ (code∈limit χ))
      (paramSet∈ σ oσ k g))

-- =====================================================================
-- BLOCK 2: THE CONTRAST, so the two arms are measured in one file.
--
-- `[LJ-1.169]`'s `prTower` is the cheapest witness of this tree's
-- delivered code shape: `n` nested pairs.  Its bound needs `2n` stages
-- and NO fixed iterate holds every depth.  BLOCK 1's bound is 5, for
-- every formula.
-- =====================================================================

dbl : ℕ → ℕ
dbl zero    = zero
dbl (suc n) = suc (suc (dbl n))

prTower : ℕ → S → S
prTower zero    x = x
prTower (suc n) x = pr (prTower n x) (prTower n x)

prTower-level : (n : ℕ) (σ x : S) → ⟨ x ∈ˢ Lset σ ⟩
              → ⟨ prTower n x ∈ˢ Lset (sucIter (dbl n) σ) ⟩
prTower-level zero    σ x h = h
prTower-level (suc n) σ x h =
  pr∈Lset-suc (sucIter (dbl n) σ) (prTower n x) (prTower n x)
    (prTower-level n σ x h) (prTower-level n σ x h)

-- ARM A's absorber, re-checked here so both arms sit side by side.
prTower-ω : (n : ℕ) (σ x : S) → ⟨ x ∈ˢ Lset σ ⟩
          → ⟨ prTower n x ∈ˢ Lset (+ω σ) ⟩
prTower-ω n σ x h = Lset-mono {α = +ω σ} {β = sucIter (dbl n) σ}
  (+ω-iter (dbl n) σ) {x = prTower n x} (prTower-level n σ x h)

-- =====================================================================
-- BLOCK 3: THE DELIVERED SPLIT FEEDS BLOCK 1 WITH NO NEW CODING.
--
-- `absFo` and `constantsFo` are delivered and GENERIC in the constant
-- type (`src/FOL/Manipulation/Parameters.lagda.md:260-261`, `:105`).
-- `nameOf` already pairs them (`src/L/Choice/Name.lagda.md:381`).  This
-- block instantiates BLOCK 1 at exactly that triple, so the uniform
-- bound holds for EVERY formula over the carrier, with `⌜_⌝` unchanged.
-- =====================================================================

deliveredSplit : (σ : S) (φ : Formula ⟪ Lset σ ⟫ 1) → S
deliveredSplit σ φ = splitKey σ 1 (countFo φ)
  (absFo {ℓz = ℓ} {n = 1} φ) (λ i → lookup i (constantsFo φ))

deliveredSplit∈ : (σ : S) (oσ : IsOrd σ) (ω∈ : ⟨ ω ∈ˢ σ ⟩)
                  (φ : Formula ⟪ Lset σ ⟫ 1)
                → ⟨ deliveredSplit σ φ ∈ˢ Lset (sucIter 5 σ) ⟩
deliveredSplit∈ σ oσ ω∈ φ = splitKey∈ σ oσ ω∈ 1 (countFo φ)
  (absFo {ℓz = ℓ} {n = 1} φ) (λ i → lookup i (constantsFo φ))

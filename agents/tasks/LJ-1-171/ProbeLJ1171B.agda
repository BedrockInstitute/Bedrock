{-# OPTIONS --cubical --safe --guardedness #-}

-- LJ-1.171 probe B.  A COPY of `agents/tasks/LJ-1-170/ProbeLJ1170A.agda`
-- BLOCK 1, extended.  Theirs is NOT edited.
--
-- WHY THIS EXISTS.  Probe A found that the parameter component must be
-- a SEQUENCE, not a set, because the reading direction recovers a
-- VECTOR and a `finSet` keeps no index
-- (`src/L/Axioms/Basic.lagda.md:285-294`).  That changes the ingredient
-- `[LJ-1.170]` measured, so `[LJ-1.170]`'s bound must be re-measured
-- at its own site rather than transferred by analogy (`LESSONS` P-l).
--
-- CRITERIA, FIXED IN WRITING BEFORE THE FIRST `agda` INVOCATION (D-1):
--   wall clock  10 minutes per agda invocation, GHCRTS="-A64m -I0 -M8g",
--               ONE process, cap NEVER raised.
--   the target  GO if the key with the SEQUENCE parameter component
--               still lands at a FIXED finite iterate above the
--               carrier, uniformly in the formula and in the number of
--               parameters, at or below 60 in-fence lines.  NO-GO if
--               the bound needs the formula's depth or the parameter
--               count, or above 60 lines.
--   counting    non-blank, non-comment lines.
--
-- P-i [F] is obeyed: every implicit set index at a concrete argument is
-- written out.  No master is edited.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-171.ProbeLJ1171B {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

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
open import L.Coding.Environment {ℓ} using ( env )
open import L.Coding.InL {ℓ} using ( envIsFinSet )
open import L.Choice.Name {ℓ} lem using ( numeral∈limit; code∈limit )
open import L.Ordinal.StageArith {ℓ} lem using ( sucIter; sucIter-ord )

open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Data.FinData using ( toℕ )
open import Cubical.Data.Vec using ( lookup )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; ∈∈ₛ; ∈ₛ⟪_⟫↪_; ∈-asFiber )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( #_; ω; sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- COPIED VERBATIM from `agents/tasks/LJ-1-170/ProbeLJ1170A.agda:95-104`.
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

-- THE CHANGED INGREDIENT.  `[LJ-1.170]` wrote `finSet k (λ i → ...)`.
-- This is the same family read as a SEQUENCE, which is what the
-- delivered `env` is (`src/L/Coding/Environment.lagda.md:84-86`).
paramEnv : (σ : S) (k : ℕ) (g : Fin k → ⟪ Lset σ ⟫) → S
paramEnv σ k g = env (λ i → ⟪ Lset σ ⟫↪ (g i))

-- THE RE-MEASUREMENT.  Two stages dearer than `[LJ-1.170]`'s set: the
-- index pairs cost two, the span costs one.  Still a FIXED iterate,
-- uniform in `k`.
paramEnv∈ : (σ : S) (oσ : IsOrd σ) (ω∈ : ⟨ ω ∈ˢ σ ⟩) (k : ℕ)
            (g : Fin k → ⟪ Lset σ ⟫)
          → ⟨ paramEnv σ k g ∈ˢ Lset (sucIter 3 σ) ⟩
paramEnv∈ σ oσ ω∈ k g =
  subst (λ w → ⟨ paramEnv σ k g ∈ˢ w ⟩) (sym (Lset-suc (sucIter 2 σ)))
    (subst (λ w → ⟨ w ∈ˢ 𝒟ₒ (Lset (sucIter 2 σ)) ⟩)
      (cong (finSet k) (funExt (λ i → fib i .snd)) ∙ sym (envIsFinSet h))
      (FinOf.finSet∈𝒟ₒ (sucIter 2 σ) (sucIter-ord 2 oσ) k (λ i → fib i .fst)))
  where
  h : Fin k → S
  h i = ⟪ Lset σ ⟫↪ (g i)

  pair∈ : (i : Fin k) → ⟨ pr (# (toℕ i)) (h i) ∈ˢ Lset (sucIter 2 σ) ⟩
  pair∈ i = pr∈Lset-suc σ (# (toℕ i)) (h i)
    (Lset-mono {α = σ} {β = ω} ω∈ {x = # (toℕ i)} (numeral∈limit (toℕ i)))
    (∈∈ₛ {a = h i} {b = Lset σ} .snd (∈ₛ⟪ Lset σ ⟫↪ (g i)))

  fib : (i : Fin k) → Σ[ m ∈ ⟪ Lset (sucIter 2 σ) ⟫ ]
          (⟪ Lset (sucIter 2 σ) ⟫↪ m ≡ pr (# (toℕ i)) (h i))
  fib i = ∈-asFiber {a = pr (# (toℕ i)) (h i)} {b = Lset (sucIter 2 σ)}
            (pair∈ i)

-- THE KEY, with the sequence in place of the set.  `sucIter 7` where
-- `[LJ-1.170]` had `sucIter 5`, and neither the depth of `χ` nor `k`
-- appears in the bound.
splitKeyE : (σ : S) (n k : ℕ) (χ : Formula (⊥* {ℓ}) (n + k))
            (g : Fin k → ⟪ Lset σ ⟫) → S
splitKeyE σ n k χ g = pr (# n) (pr VCode.⌜ embed χ ⌝ (paramEnv σ k g))

splitKeyE∈ : (σ : S) (oσ : IsOrd σ) (ω∈ : ⟨ ω ∈ˢ σ ⟩) (n k : ℕ)
             (χ : Formula (⊥* {ℓ}) (n + k)) (g : Fin k → ⟪ Lset σ ⟫)
           → ⟨ splitKeyE σ n k χ g ∈ˢ Lset (sucIter 7 σ) ⟩
splitKeyE∈ σ oσ ω∈ n k χ g =
  pr∈Lset-suc (sucIter 5 σ) (# n) (pr VCode.⌜ embed χ ⌝ (paramEnv σ k g))
    (fromω σ ω∈ 4 (# n) (numeral∈limit n))
    (pr∈Lset-suc (sucIter 3 σ) VCode.⌜ embed χ ⌝ (paramEnv σ k g)
      (fromω σ ω∈ 2 VCode.⌜ embed χ ⌝ (code∈limit χ))
      (paramEnv∈ σ oσ ω∈ k g))

-- The delivered split feeds it unchanged, exactly as `[LJ-1.170]`
-- BLOCK 3 did.  `⌜_⌝` is not touched.
deliveredSplitE : (σ : S) (φ : Formula ⟪ Lset σ ⟫ 1) → S
deliveredSplitE σ φ = splitKeyE σ 1 (countFo φ)
  (absFo {ℓz = ℓ} {n = 1} φ) (λ i → lookup i (constantsFo φ))

deliveredSplitE∈ : (σ : S) (oσ : IsOrd σ) (ω∈ : ⟨ ω ∈ˢ σ ⟩)
                   (φ : Formula ⟪ Lset σ ⟫ 1)
                 → ⟨ deliveredSplitE σ φ ∈ˢ Lset (sucIter 7 σ) ⟩
deliveredSplitE∈ σ oσ ω∈ φ = splitKeyE∈ σ oσ ω∈ 1 (countFo φ)
  (absFo {ℓz = ℓ} {n = 1} φ) (λ i → lookup i (constantsFo φ))

{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.651] PROBE.  The Lset graph as a FORMULA over the hull's alphabet.
-- It runs in agents/tasks/LJ-1-651/ and lands nothing in src/.
--
--   THE OBLIGATION  lset-formula.  The level-hood matrix, the tree's
--                   Sigma-0 matrix, read at two slots with the bound K
--                   existentially closed and the ordinal and the value
--                   in SLOTS, then instantiated at the hull's code
--                   alphabet.  NOT wit at absFo LsetGraph: that route
--                   is dead at its grade (2,287 unbounded ∃̇ and 2,159
--                   unbounded ∀̇, agents/tasks/LJ-1-646/lj-1.646-report.md:82
--                   and :278-280).
--
--   THE ROUTE  [LJ-1.646] named it: a reading of levelHoodB at two
--              slots, then its instantiation at the hull's code
--              alphabet (agents/tasks/LJ-1-646/lj-1.646-report.md:281-285).
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M2g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-651.Probe651 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _∈̇_; _≐_; _∧̇_; ⊤̇; ∃̇_ )
open import FOL.LevyHierarchy using ( Δ₀; Σ₁; σ-Δ₀; σ-∃ )
open import FOL.Manipulation.Parameters using ( countFo )
open import FOL.Manipulation.Relabelling using ( mapFo )
open import FOL.Manipulation.Renaming using ( renameFo )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; Lset; 𝒮ʟ )
open import L.Hull {ℓ} lem using ( module AtStage )
open import L.BoundedSubset {ℓ} lem using ( module LevelHood0 )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; module InfinitySet )
open InfinitySet using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
module CS = hPropStructure 𝒮ʟ

-- Telescope copied from src/L/BoundedSubset.lagda.md:903-906.
-- Nothing below the copied rows is copied.

module HullStage (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : S) (X⊆L : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Lset lam ⟩) (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  module ASt = AtStage lam ordλ

  module H = ASt.Hull X X⊆L ∅∈λ

  open H.T using ( Code; wit )

  -- =====================================================================
  -- THE MATRIX.  levelHoodB at n = 0: env u ∷ v ∷ γ ∷ K,
  -- "exists w in K (graph w gamma K and v = w)"
  -- (src/L/BoundedSubset.lagda.md:107-111), Δ₀ at LH0.Δ₀-matrix.
  -- The 16 Fin slot positions are all zero, the delivered convention:
  -- agents/tasks/archive/LJ-1-50/ProbeDD25H5.agda:47-49.
  -- =====================================================================

  module LH0 = LevelHood0
    zero zero zero zero zero zero zero zero zero zero zero zero zero zero
    zero zero zero zero zero zero zero zero zero zero zero zero zero zero

  -- The matrix carries no constant: no con node.  Same term at
  -- agents/tasks/archive/LJ-1-50/ProbeDD25H5.agda:55-56.
  count-matrix : countFo LH0.matrix ≡ 0
  count-matrix = refl

  -- =====================================================================
  -- THE TWO-SLOT READING, at the class carrier, step by step.
  -- =====================================================================

  -- STEP 1.  Close the unused u slot: env v ∷ γ ∷ K.
  step1 : Formula CS.S 3
  step1 = ∃̇ LH0.matrix

  -- Grade: one unbounded ∃̇ over the Δ₀ matrix, so Sigma-1.  The tree
  -- delivers this certificate for the same term
  -- (src/L/BoundedSubset.lagda.md:145-146).
  Σ₁-step1 : Σ₁ step1
  Σ₁-step1 = σ-∃ (σ-Δ₀ LH0.Δ₀-matrix)

  -- STEP 2.  Rotate K to the front: env K ∷ v ∷ γ.
  rot : Fin 3 → Fin 3
  rot zero           = suc zero
  rot (suc zero)     = suc (suc zero)
  rot (suc (suc zero)) = zero

  step2 : Formula CS.S 3
  step2 = renameFo rot step1

  -- STEP 3.  Close the bound K by the unbounded existential: env v ∷ γ.
  step3 : Formula CS.S 2
  step3 = ∃̇ step2

  -- STEP 4.  Swap to the consumer order, ordinal slot 0 and value slot 1,
  -- the order of [LJ-1.642]'s Det/Wit/Holds
  -- (agents/tasks/LJ-1-642/Probe642.agda:91-97): env γ ∷ v.
  swap : Fin 2 → Fin 2
  swap zero       = suc zero
  swap (suc zero) = zero

  twoSlot : Formula CS.S 2
  twoSlot = renameFo swap step3

  -- The reading carries no constant: the quantifiers and the renames
  -- move variables only, and the matrix has none.
  count-twoSlot : countFo twoSlot ≡ 0
  count-twoSlot = refl

  -- =====================================================================
  -- THE INSTANTIATION AT THE HULL'S CODE ALPHABET.
  -- =====================================================================

  -- The carrier slide CS.S → Code.  count-twoSlot says the formula
  -- carries no constant, so mapFo never evaluates slide: any code
  -- will do, and wit supplies one with no hypothesis on X.
  slide-φ : Formula (⊥* {ℓ}) 1
  slide-φ = ⊤̇

  slide : CS.S → Code
  slide _ = wit 0 slide-φ []

  -- =====================================================================
  -- OBLIGATION.
  -- =====================================================================

  -- "value = Lset ordinal" in the hull's language: the Sigma-0 reading
  -- of the level-hood matrix at the two slots, the ordinal in slot 0
  -- and the value in slot 1, the bound K existentially closed.  Grade:
  -- 2 unbounded ∃̇ and 0 unbounded ∀̇ over the Δ₀ core, so Sigma-1, and
  -- the tree's transfer σ₁-up applies
  -- (src/FOL/Absoluteness.lagda.md:182-184).
  lset-formula : Formula Code 2
  lset-formula = mapFo slide twoSlot

  -- THE ARITY-1 READING, the shape hull-closed takes
  -- (src/L/Hull.lagda.md:415): for a fixed ordinal code c, close the
  -- ordinal slot to its code and keep the value slot: "x is the Lset
  -- of val c".  This is [LJ-1.642]'s inF with lset-formula for ψ
  -- (agents/tasks/LJ-1-642/Probe642.agda:158-159).
  inF : (c : Code) → Formula Code 1
  inF c = ∃̇ (lset-formula ∧̇ (var zero ≐ con c))

-- The witness meter reads `Target.lset-formula` at this module
-- (scripts/pod/witness.py:278). A named parameterised module does not
-- lift the name. The term above is the one the brief wrote.

lset-formula = HullStage.lset-formula

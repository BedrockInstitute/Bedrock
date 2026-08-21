{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.474] PROBE.  Hull codes for the constants of LsetGraph.
-- It runs in agents/tasks/LJ-1-474/ and lands nothing in src/.
--
--   STEP ONE, W3 FIRST  zero-code.  Route 1 from [LJ-1.472]:
--                       wit at ∀̇∈ (var zero) ⊥̇.  Obligation omitted
--                       in the W3-only file.  Code quoted from
--                       Probe472.agda:108-109.
--
--   STEP TWO            lset-codes.  Map ck along constantsFo.
--                       ck quoted from Probe472.agda:210-211.
--                       tagOf recovers k from numeralL k by lem,
--                       bound 12 from [LJ-1.466]'s census.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-474.Probe474 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _∈̇_; _≐_; _∧̇_; _∨̇_; ⊥̇; ∀̇∈; ∃̇∈ )
open import FOL.Manipulation.Parameters using ( absFo; countFo; constantsFo )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; Lset; 𝒮ʟ )
open import L.Hull {ℓ} lem using ( module AtStage )
open import L.Axioms.Numerals {ℓ} using ( numeralL )
open import L.Coding.Sequence {ℓ} lem using ( LsetGraph )

open import Cubical.Data.Nat using ( ℕ; _+_ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Vec using ( Vec; _∷_; []; map )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; module InfinitySet )
open InfinitySet using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
module CS = hPropStructure 𝒮ʟ

-- W2: formulas once, generic in the constant domain.  Instantiated at
-- ⊥* for wit.  Same terms as [LJ-1.472], copied from
-- archive/src/2026-08-09-rud-route/L/Cardinal.lagda.md:367-373.
-- Not a named term in live src/.  Do not import a probe.

succFo : ∀ {ℓk} {K : Type ℓk} {n} (x y : Fin n) → Formula K n
succFo x y =
    (∀̇∈ (var y) ((var zero ∈̇ var (suc x)) ∨̇ (var zero ≐ var (suc x))))
  ∧̇ (∀̇∈ (var x) (var zero ∈̇ var (suc y)))
  ∧̇ (var x ∈̇ var y)

numeralFo : (n : ℕ) → ∀ {ℓk} {K : Type ℓk} {n'} (v : Fin (suc n'))
          → Formula K (suc n')
numeralFo zero v = ∀̇∈ (var v) ⊥̇
numeralFo (suc n) {ℓk} {K} {n'} v =
  ∃̇∈ (var v) (succFo zero (suc v) ∧̇ numeralFo n {K = K} {n' = suc n'} zero)

-- Packaging from [LJ-1.462], Probe462.agda:66-67.
packaged : Formula (⊥* {ℓ}) (2 + countFo LsetGraph)
packaged = absFo {ℓz = ℓ} LsetGraph

consts : Vec CS.S (countFo LsetGraph)
consts = constantsFo LsetGraph

-- Decoder.  [LJ-1.466] census, lj-1.466-report.md:188-189: every visible
-- con is numeralL k for k ∈ {0,1,...,11}.  Search those twelve tags.
-- Default 0 if none match.  No hypothesis on X.

tagBound : ℕ
tagBound = 12

tagFrom : ℕ → ℕ → CS.S → ℕ
tagFrom k zero s = 0
tagFrom k (suc r) s with lem ((s ≡ numeralL k) , CS.isSetS s (numeralL k))
... | inl _ = k
... | inr _ = tagFrom (suc k) r s

tagOf : CS.S → ℕ
tagOf s = tagFrom 0 tagBound s

-- Telescope copied from src/L/BoundedSubset.lagda.md:903-914.
-- Nothing below module Condense is copied.

module HullStage (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : S) (X⊆L : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  module ASt = AtStage lam ordλ

  module H = ASt.Hull X X⊆L ∅∈λ

  M : S
  M = H.T.Hull

  open H.T using ( Code; wit )

  -- =====================================================================
  -- W3.  The code for numeralL 0.
  -- Quote: agents/tasks/LJ-1-472/Probe472.agda:108-109.
  -- =====================================================================

  φ0 : Formula (⊥* {ℓ}) 1
  φ0 = ∀̇∈ (var zero) ⊥̇

  zero-code : Code
  zero-code = wit 0 φ0 []

  -- =====================================================================
  -- Obligation.  Route 1, the code, not the membership.
  -- Quote: agents/tasks/LJ-1-472/Probe472.agda:210-211.
  -- =====================================================================

  φk : (k : ℕ) → Formula (⊥* {ℓ}) 1
  φk k = numeralFo k {n' = 0} zero

  ck : (k : ℕ) → Code
  ck k = wit 0 (φk k) []

  lset-codes : Vec Code (countFo LsetGraph)
  lset-codes = map (λ s → ck (tagOf s)) consts

  -- [LJ-1.462] feed, Probe462.agda:101-102, now with the extra Vec filled.
  -- Not lset-code.  Not levelIn.

  feed : (c : Code) → Code
  feed c = wit (suc (countFo LsetGraph)) packaged (c ∷ lset-codes)

-- The witness meter reads `Target.lset-codes` at this module
-- (`scripts/pod/witness.py:278`). A named parameterised module does not
-- lift the name. The term above is the one the brief wrote.

lset-codes = HullStage.lset-codes

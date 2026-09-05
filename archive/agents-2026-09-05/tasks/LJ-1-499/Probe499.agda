{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.499] The envK family of TFacts at KValue's frame.
--
-- W3 FIRST, and alone: envInK at KValue's frame.
--
-- D-10 SETTLED BEFORE ANY AGDA (see lj-1.499-report.md).  The brief
-- names `module EnvSet` (src/L/Condensation.lagda.md:2929) as the
-- supplier.  It cannot be: `E∈K` is EnvSet's THIRD argument
-- (:2934) and it is exactly what every `envK-*` field CONCLUDES
-- (src/L/Condensation/TwelveAgree.lagda.md:191).  EnvSet consumes
-- the goal.  The tree's own supplier is `SupplyEnv.envK-gen`
-- (src/L/Coding/EnvSupply.lagda.md:277), and `someEnv`
-- (:417-444) shows the true direction: it BUILDS `EK` by
-- `envSetK` (:433) and then FEEDS EnvSet (:440).
--
-- W3 is NOT circular against a TFacts value.  It is delivered by
-- `SupplyEnv.envInK-gen` (src/L/Coding/EnvSupply.lagda.md:351)
-- under two ties the brief's type omits: `arNum` and `arK`.
-- TFacts states envInK-mem with BOTH of them
-- (src/L/Condensation/TwelveAgree.lagda.md:216-222), so the tied
-- form below is the record's own form and not a weakening.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide
-- caliber, set on the pane by the program and untouched here.
-- Nothing lands in src/.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-499.Probe499 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; IsOrd )
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import L.Coding.Model {ℓ} using ( envSetAt; envOverAt )
open import L.Condensation {ℓ} lem using ( module KValue; module KFactsNS )
open import L.Coding.EnvSupply {ℓ} lem using ( module SupplyEnv )
open import Cubical.Data.Nat using ( ℕ; _+_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; ∅ )
open InfinitySet {ℓ} using ( #_; sucV; ω )
open import Cubical.HITs.PropositionalTruncation using ( ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ
open KFactsNS

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- =====================================================================
-- THE FRAME.  KValue's telescope, plus SupplyEnv's own ω hypothesis.
--
--   [LJ-1.491] delivered KValue's telescope plus ⟨ ω ∈ gam ⟩
--   (agents/tasks/LJ-1-491/Probe491.agda:59, GO at
--   agents/tasks/LJ-1-491/lj-1.491-report.md:76).  SupplyEnv states
--   the same hypothesis one successor out, ⟨ ω ∈ sucV gam ⟩
--   (src/L/Coding/EnvSupply.lagda.md:111).  This frame takes
--   SupplyEnv's form, because SupplyEnv is the module that supplies
--   the family and its type is the one it delivers.
-- =====================================================================

module Frame
  (lam : V ℓ) (ordλ : IsOrd lam)
  (succλ : (d : V ℓ) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ lam ⟩)
  (gam : V ℓ) (ordγ : IsOrd gam) (γ∈λ : ⟨ gam ∈ lam ⟩)
  (ω∈σ : ⟨ ω ∈ sucV gam ⟩) where

  module KV = KValue lam ordλ succλ ∅∈λ gam ordγ γ∈λ
  module SE = SupplyEnv lam ordλ succλ ∅∈λ gam ordγ γ∈λ ω∈σ

  -- The six slots TFacts prepends to its Fin (5 + n) block.  Slot 0 is
  -- the B slot of every envK-* and every envInK-* field, so it carries
  -- the carrier B₀ = LsetS gam ordγ (src/L/Coding/EnvSupply.lagda.md
  -- :124-125).  That is what `envK-gen`'s `qb` asks and what the
  -- delivered five already do (:302, :313, :324, :336, :348).  Five free.
  gam' : (g1 g2 g3 g4 g5 : S) → Vec S 20
  gam' g1 g2 g3 g4 g5 = SE.B₀ ∷ g1 ∷ g2 ∷ g3 ∷ g4 ∷ g5 ∷ KV.Kenv

  -- ===================================================================
  -- W3.  envInK at KValue's frame, in the TIED form TFacts states.
  --   Type copied from src/L/Condensation/TwelveAgree.lagda.md:216-222
  --   with K := KV.iK and γ' := gam' g1 g2 g3 g4 g5.
  -- ===================================================================
  envInK-at-frame :
      (g1 g2 g3 g4 g5 : S)
    → (yc b a ar c E : S)
    → ⟨ fst ar ∈ fst (lookup (suc (suc (suc (suc (suc (suc KV.iK))))))
                        (gam' g1 g2 g3 g4 g5)) ⟩
    → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
    → (z : S) → ⟨ (z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ gam' g1 g2 g3 g4 g5) ⊨
        envOverAt zero (suc (suc (suc (suc (suc zero)))))
                       (suc (suc (suc (suc (suc (suc (suc zero))))))) ⟩
    → ⟨ fst z ∈ fst (lookup (suc (suc (suc (suc (suc (suc KV.iK))))))
                       (gam' g1 g2 g3 g4 g5)) ⟩
  envInK-at-frame g1 g2 g3 g4 g5 yc b a ar c E arK arNum z h =
    SE.envInK-gen (E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ gam' g1 g2 g3 g4 g5)
      (suc (suc (suc (suc zero))))
      (suc (suc (suc (suc (suc (suc zero))))))
      refl arNum arK z h


-- =====================================================================
-- THE OBLIGATION'S TYPE.  The five envK-* fields of TFacts, once,
--   at TFacts's own indices.  Copied verbatim from
--   src/L/Condensation/TwelveAgree.lagda.md:186-215.  The five name
--   only `K` and `γ'` of that record's parameters, so only those two
--   are stated here (W2: the block is written ONCE and instantiated).
-- =====================================================================

record EnvK5 {n : ℕ} (K : Fin (5 + n)) (γ' : Vec S (11 + n))
  : Type (ℓ-suc ℓ) where
  field
    envK-mem : (yc b a ar c E : S)
               → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
               → ⟨ (E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨
                 envSetAt zero (suc (suc (suc (suc zero))))
                           (suc (suc (suc (suc (suc (suc zero)))))) ⟩
              → ⟨ fst E ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
    envK-neg : (ya yc a ar c E : S)
               → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
               → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ') ⊨
                 envSetAt zero (suc (suc (suc (suc zero))))
                           (suc (suc (suc (suc (suc (suc zero)))))) ⟩
              → ⟨ fst E ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
    envK-top : (yc a ar c E : S)
               → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
               → ⟨ (E ∷ yc ∷ a ∷ ar ∷ c ∷ γ') ⊨
                 envSetAt zero (suc (suc (suc zero)))
                           (suc (suc (suc (suc (suc zero))))) ⟩
              → ⟨ fst E ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
    envK-imp : (E yb ya yc b a ar c : S)
               → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
               → ⟨ (E ∷ yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨
                 envSetAt zero (suc (suc (suc (suc (suc (suc zero))))))
                           (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) ⟩
              → ⟨ fst E ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
    envK-allin : (E ya yc b a ar c : S)
               → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
               → ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨
                   envSetAt zero (suc (suc (suc (suc (suc zero)))))
                             (suc (suc (suc (suc (suc (suc (suc zero))))))) ⟩
                → ⟨ fst E ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩

module Obligation
  (lam : V ℓ) (ordλ : IsOrd lam)
  (succλ : (d : V ℓ) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ lam ⟩)
  (gam : V ℓ) (ordγ : IsOrd gam) (γ∈λ : ⟨ gam ∈ lam ⟩)
  (ω∈σ : ⟨ ω ∈ sucV gam ⟩) where

  open Frame lam ordλ succλ ∅∈λ gam ordγ γ∈λ ω∈σ

  -- THE OBLIGATION.  Every field is ONE application of the tree's own
  -- slot-generic shell `SupplyEnv.envK-gen`
  -- (src/L/Coding/EnvSupply.lagda.md:277-291).  `refl` discharges its
  -- `qb`, because slot 0 of γ' is B₀ by construction of `gam'`.
  envK-family : (g1 g2 g3 g4 g5 : S)
              → EnvK5 {n = 9} KV.iK (gam' g1 g2 g3 g4 g5)
  envK-family g1 g2 g3 g4 g5 = record
    { envK-mem = λ yc b a ar c E arNum h →
        SE.envK-gen (E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ gam' g1 g2 g3 g4 g5)
          zero (suc (suc (suc (suc zero))))
          (suc (suc (suc (suc (suc (suc zero))))))
          refl arNum h
    ; envK-neg = λ ya yc a ar c E arNum h →
        SE.envK-gen (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ gam' g1 g2 g3 g4 g5)
          zero (suc (suc (suc (suc zero))))
          (suc (suc (suc (suc (suc (suc zero))))))
          refl arNum h
    ; envK-top = λ yc a ar c E arNum h →
        SE.envK-gen (E ∷ yc ∷ a ∷ ar ∷ c ∷ gam' g1 g2 g3 g4 g5)
          zero (suc (suc (suc zero)))
          (suc (suc (suc (suc (suc zero)))))
          refl arNum h
    ; envK-imp = λ E yb ya yc b a ar c arNum h →
        SE.envK-gen (E ∷ yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ gam' g1 g2 g3 g4 g5)
          zero (suc (suc (suc (suc (suc (suc zero))))))
          (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
          refl arNum h
    ; envK-allin = λ E ya yc b a ar c arNum h →
        SE.envK-gen (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ gam' g1 g2 g3 g4 g5)
          zero (suc (suc (suc (suc (suc zero)))))
          (suc (suc (suc (suc (suc (suc (suc zero)))))))
          refl arNum h }

envInK-at-frame = Frame.envInK-at-frame
envK-family = Obligation.envK-family

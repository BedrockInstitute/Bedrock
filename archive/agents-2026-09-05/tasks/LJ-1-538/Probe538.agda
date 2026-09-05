{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.538] The NINE env forms of TFacts, collected at KValue's frame.
--
-- W3 FIRST, and alone: the nine hypotheses as ONE telescope, stated and
-- typechecked, NO witness.  This is the file at the W3 run.  The frame
-- and the witness are appended after that run lands.
--
-- WHY NINE AND NOT SIXTEEN.  The brief reports that [LJ-1.534] took
-- all sixteen at one frame and matched a heap wall four times, exit
-- 251 each, and cites dev/pod/transitions/2026-08.jsonl.  I COULD NOT
-- CHECK THAT CITATION HERE: the tracked copy in this worktree ends at
-- seq 158, task LJ-1.399, ts 2026-08-19T13:31:57Z, and carries no
-- LJ-1.534 record (`grep -c LJ-1-534` gives 0).  The claim is the
-- brief's and it is repeated as the brief's, not confirmed.  No
-- agents/tasks/LJ-1-534/ directory exists here either, so the brief's
-- "no report and no probe" is the one half I can confirm.
-- This file takes the family that is already delivered whole:
-- src/L/Coding/EnvSupply.lagda.md:293-411 holds all nine, and
-- [LJ-1.499] measured that they reach TFacts's frame with one `refl`
-- each (agents/tasks/LJ-1-499/lj-1.499-report.md:277-279).
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber,
-- set on the pane by the program and untouched here.  Nothing lands in
-- src/.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-538.Probe538 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

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
-- W3.  THE NINE HYPOTHESES AS ONE TELESCOPE.  No witness.
--
--   The five `envK-*` and the four `envInK-*` fields of TFacts, once,
--   at TFacts's own indices.  Copied verbatim from
--   src/L/Condensation/TwelveAgree.lagda.md:186-243.  The nine name
--   only `K` and `γ'` of that record's parameters, so only those two
--   are stated here (W2: the block is written ONCE and instantiated).
--
--   The other seven TFacts env-side fields are NOT here.  AD12 gives
--   this task one obligation, and [LJ-1.534] measured what the whole
--   set costs.
-- =====================================================================

record EnvNine {n : ℕ} (K : Fin (5 + n)) (γ' : Vec S (11 + n))
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
    envInK-mem : (yc b a ar c E : S)
               → ⟨ fst ar ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
               → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
               → (z : S) → ⟨ (z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨
                   envOverAt zero (suc (suc (suc (suc (suc zero)))))
                               (suc (suc (suc (suc (suc (suc (suc zero))))))) ⟩
                → ⟨ fst z ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
    envInK-neg : (ya yc a ar c E : S)
               → ⟨ fst ar ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
               → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
               → (z : S) → ⟨ (z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ') ⊨
                   envOverAt zero (suc (suc (suc (suc (suc zero)))))
                               (suc (suc (suc (suc (suc (suc (suc zero))))))) ⟩
                → ⟨ fst z ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
    envInK-top : (yc a ar c E : S)
               → ⟨ fst ar ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
               → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
               → (z : S) → ⟨ (z ∷ E ∷ yc ∷ a ∷ ar ∷ c ∷ γ') ⊨
                   envOverAt zero (suc (suc (suc (suc zero))))
                               (suc (suc (suc (suc (suc (suc zero)))))) ⟩
                → ⟨ fst z ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
    envInK-imp : (E ya yc b a ar c : S)
               → ⟨ fst ar ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
               → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
               → (z : S) → ⟨ (z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨
                   envOverAt zero (suc (suc (suc (suc (suc (suc zero))))))
                               (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) ⟩
                → ⟨ fst z ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩

-- =====================================================================
-- THE FRAME.  The extra hypotheses the NINE forms take, collected as
-- ONE telescope.  These are the module parameters below, so the
-- projected name `Frame.envK-frame-inhabited` carries the telescope as
-- explicit arguments and the top-level alias at the foot of this file
-- IS "telescope → witness".
--
-- D-10, MEASURED BEFORE ANY AGDA (see lj-1.538-report.md).  The
-- telescope is `SupplyEnv`'s own, eight parameters
-- (src/L/Coding/EnvSupply.lagda.md:107-111).  SEVEN of the eight are
-- KValue's telescope word for word (src/L/Condensation.lagda.md
-- :7380-7383).  The eighth, `ω∈σ : ⟨ ω ∈ sucV gam ⟩`
-- (src/L/Coding/EnvSupply.lagda.md:111), is the ONE hypothesis KValue
-- does not carry.
--
-- ONE OF THE EIGHT IS NOT USED BY THE NINE.  `ordλ` reaches the nine
-- only through `module B = Bound lam ordλ succλ ∅∈λ`
-- (src/L/Coding/EnvSupply.lagda.md:113), and every step of that path
-- is by `succλ` and `∅∈λ` alone: `#∈λ` (src/L/Coding/Bound.lagda.md
-- :55-57, "by the two parameters alone" at :54) and `suc^∈λ` (:97-99).
-- `ordλ` is REQUIRED TO STATE the frame, because `KV.Kenv`'s bound
-- slot is `LsetS lam ordλ` (src/L/Condensation.lagda.md:7390), but
-- `LsetS β oβ = Lset β , isL-Lset β oβ`
-- (src/L/Axioms/Basic.lagda.md:161) puts it in the `snd`, and every
-- one of the nine projects the slot by `fst`.  It is carried, and no
-- proof below consumes it.
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
  -- delivered nine already do (src/L/Coding/EnvSupply.lagda.md:302,
  -- :313, :324, :336, :348, :374, :386, :398, :411).  Five free.
  -- Identical to [LJ-1.499]'s `gam'` (Probe499.agda:83-84), which is
  -- GO (agents/tasks/LJ-1-499/lj-1.499-report.md:20).
  gam' : (g1 g2 g3 g4 g5 : S) → Vec S 20
  gam' g1 g2 g3 g4 g5 = SE.B₀ ∷ g1 ∷ g2 ∷ g3 ∷ g4 ∷ g5 ∷ KV.Kenv

  -- ===================================================================
  -- THE OBLIGATION.  NON-VACUITY: the telescope alone is not the
  -- deliverable ([LJ-1.507], agents/tasks/LJ-1-507/Probe507.agda:257).
  --
  -- Every field is ONE application of the tree's own slot-generic
  -- shell, `SupplyEnv.envK-gen` (src/L/Coding/EnvSupply.lagda.md:277)
  -- for the five and `SupplyEnv.envInK-gen` (:351) for the four.
  -- `refl` discharges `qb` in all nine, because slot 0 of γ' is B₀ by
  -- construction of `gam'`.  The `di` and `bi` numerals are the ones
  -- the delivered forms already use (:301, :312, :323, :334, :346,
  -- :373, :385, :397, :409); the frame moves only the TAIL of the
  -- vector, from `B₀ ∷ []` to `γ'`, and B₀ keeps its index.
  --
  -- The four envInK-* fields take `arK` BEFORE `arNum`
  -- (src/L/Condensation/TwelveAgree.lagda.md:217-218) and
  -- `envInK-gen` takes them the other way round
  -- (src/L/Coding/EnvSupply.lagda.md:353-354).  The swap is in the
  -- applications below and it is the record's order that wins.
  -- ===================================================================
  envK-frame-inhabited : (g1 g2 g3 g4 g5 : S)
                       → EnvNine {n = 9} KV.iK (gam' g1 g2 g3 g4 g5)
  envK-frame-inhabited g1 g2 g3 g4 g5 = record
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
          refl arNum h
    ; envInK-mem = λ yc b a ar c E arK arNum z h →
        SE.envInK-gen (E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ gam' g1 g2 g3 g4 g5)
          (suc (suc (suc (suc zero))))
          (suc (suc (suc (suc (suc (suc zero))))))
          refl arNum arK z h
    ; envInK-neg = λ ya yc a ar c E arK arNum z h →
        SE.envInK-gen (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ gam' g1 g2 g3 g4 g5)
          (suc (suc (suc (suc zero))))
          (suc (suc (suc (suc (suc (suc zero))))))
          refl arNum arK z h
    ; envInK-top = λ yc a ar c E arK arNum z h →
        SE.envInK-gen (E ∷ yc ∷ a ∷ ar ∷ c ∷ gam' g1 g2 g3 g4 g5)
          (suc (suc (suc zero)))
          (suc (suc (suc (suc (suc zero)))))
          refl arNum arK z h
    ; envInK-imp = λ E ya yc b a ar c arK arNum z h →
        SE.envInK-gen (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ gam' g1 g2 g3 g4 g5)
          (suc (suc (suc (suc (suc zero)))))
          (suc (suc (suc (suc (suc (suc (suc zero)))))))
          refl arNum arK z h }

-- THE OBLIGATION AT THE TOP LEVEL: the collected telescope, then the
-- five free slots, then the witness.
envK-frame-inhabited = Frame.envK-frame-inhabited

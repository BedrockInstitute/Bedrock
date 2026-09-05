{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.504] How far SupplyEnv's own someEnv reaches toward someEnvDef.
--
-- W3 FIRST, and alone: difference 2, the renaming.  The obligation is
-- omitted from this stage and added only if W3 lands.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber,
-- set on the pane by the program and untouched here.  Nothing lands in
-- src/.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-504.Probe504 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; IsOrd )
open import L.Condensation {ℓ} lem
  using ( module KValue; envSetB; envHypB2 )
open import L.Condensation.LowerAgree {ℓ} lem using ( someEnvDef )
open import L.Coding.EnvSupply {ℓ} lem using ( module SupplyEnv )
open import Cubical.Data.Nat using ( ℕ; _+_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; ∅ )
open InfinitySet {ℓ} using ( #_; sucV; ω )
open import Cubical.HITs.PropositionalTruncation using ( ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- =====================================================================
-- THE FRAME.  Taken from `[LJ-1.499]`'s DELIVERED probe, not from this
-- brief: `agents/tasks/LJ-1-499/Probe499.agda:68-84`, GO at
-- `agents/tasks/LJ-1-499/lj-1.499-report.md:20`.  KValue's telescope
-- plus SupplyEnv's own `⟨ ω ∈ sucV gam ⟩`, which is the gate
-- `[LJ-1.503]` settled.
-- =====================================================================

module Frame
  (lam : V ℓ) (ordλ : IsOrd lam)
  (succλ : (d : V ℓ) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ lam ⟩)
  (gam : V ℓ) (ordγ : IsOrd gam) (γ∈λ : ⟨ gam ∈ lam ⟩)
  (ω∈σ : ⟨ ω ∈ sucV gam ⟩) where

  module KV = KValue lam ordλ succλ ∅∈λ gam ordγ γ∈λ
  module SE = SupplyEnv lam ordλ succλ ∅∈λ gam ordγ γ∈λ ω∈σ

  -- Slot 0 carries the carrier B₀; five free slots; then KValue's own
  -- fourteen.  `[LJ-1.499]`'s `gam'`, unchanged.
  gam' : (g1 g2 g3 g4 g5 : S) → Vec S 20
  gam' g1 g2 g3 g4 g5 = SE.B₀ ∷ g1 ∷ g2 ∷ g3 ∷ g4 ∷ g5 ∷ KV.Kenv

  -- ===================================================================
  -- W3.  DIFFERENCE 2, and nothing else.
  --
  --   `envHypB2 {m} B K = envSetB zero (suc⁵ zero) (suc⁷ B) (suc⁷ K)`
  --   (`src/L/Condensation.lagda.md:654-658`).  So the record's
  --   conclusion and the supplier's conclusion are the SAME formula
  --   constructor at two layouts.  At this frame the four slots hit
  --   the same four values:
  --     E  : zero              -> E          | zero    -> E
  --     ar : suc⁵ zero  = 5    -> ar         | suc zero -> ar
  --     B  : suc⁷ zero  = 7    -> gam'[0]=B₀ | suc² zero -> B₀
  --     K  : suc⁷(suc⁶ iK)= 14 -> gam'[7]    | suc³ zero -> level
  --   and `gam'[7] = KV.Kenv[1] = LsetS lam ordλ = SE.level`.
  --
  --   The question this term asks is whether `_⊨_` computes far enough
  --   for those two to be the SAME TYPE, or whether the renaming needs
  --   a lemma the tree does not have.
  -- ===================================================================
  envSetB-to-envHypB2 :
      (g1 g2 g3 g4 g5 : S) (E ya yc b a ar c : S)
    → ⟨ (E ∷ ar ∷ SE.B₀ ∷ SE.level ∷ []) ⊨
          envSetB zero (suc zero) (suc (suc zero)) (suc (suc (suc zero))) ⟩
    → ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ gam' g1 g2 g3 g4 g5) ⊨
          envHypB2 {11 + 9} zero
            (suc (suc (suc (suc (suc (suc KV.iK)))))) ⟩
  envSetB-to-envHypB2 g1 g2 g3 g4 g5 E ya yc b a ar c h = h

  -- The record's K index, once.  `lookup K6 (gam' ...)` is `gam'[7]`,
  -- which is `KV.Kenv[1] = LsetS lam ordλ = SE.level`.
  K6 : Fin 20
  K6 = suc (suc (suc (suc (suc (suc KV.iK)))))

  -- ===================================================================
  -- DIFFERENCE 3, ISOLATED.  This is `someEnvDef {9} KV.iK (gam' ...)`
  -- EXACTLY, with ONE hypothesis inserted: `SupplyEnv.someEnv`'s own
  -- numeral truncation (`src/L/Coding/EnvSupply.lagda.md:419`).  The
  -- body is ONE application of the delivered supplier and nothing else,
  -- so if this term typechecks then differences 1 and 2 are BOTH closed
  -- and difference 3 is the WHOLE remaining distance.
  -- ===================================================================
  someEnv-gated :
      (g1 g2 g3 g4 g5 : S) (ya yc b a ar c : S)
    → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
    → ⟨ fst ya ∈ fst (lookup K6 (gam' g1 g2 g3 g4 g5)) ⟩
    → ⟨ fst yc ∈ fst (lookup K6 (gam' g1 g2 g3 g4 g5)) ⟩
    → ⟨ fst ar ∈ fst (lookup K6 (gam' g1 g2 g3 g4 g5)) ⟩
    → Σ S (λ E → ⟨ fst E ∈ fst (lookup K6 (gam' g1 g2 g3 g4 g5)) ⟩
        × ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ gam' g1 g2 g3 g4 g5) ⊨
              envHypB2 {11 + 9} zero K6 ⟩)
  someEnv-gated g1 g2 g3 g4 g5 ya yc b a ar c arNum yaK ycK arK =
    SE.someEnv ya yc b a ar c arNum yaK ycK arK

  -- ===================================================================
  -- THE GAP, STATED AS A TYPE.  This is the one input the record's
  -- field does not carry and the supplier asks for, at the record's own
  -- frame.  It reads: "at `KValue`'s bound, a member of K is a
  -- numeral".
  -- ===================================================================
  someEnvDef-gap : Type (ℓ-suc ℓ)
  someEnvDef-gap =
      (g1 g2 g3 g4 g5 : S) (ya yc b a ar c : S)
    → ⟨ fst ya ∈ fst (lookup K6 (gam' g1 g2 g3 g4 g5)) ⟩
    → ⟨ fst yc ∈ fst (lookup K6 (gam' g1 g2 g3 g4 g5)) ⟩
    → ⟨ fst ar ∈ fst (lookup K6 (gam' g1 g2 g3 g4 g5)) ⟩
    → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁

  -- THE DISTANCE IS EXACTLY THAT TYPE, and this term is the proof of
  -- sufficiency.  It is NOT the obligation: `someEnvDef-gap` is a
  -- hypothesis here and no term of it is built.  The obligation name
  -- `someEnv-reaches` is DELIBERATELY ABSENT from this file.  See
  -- `review-of-someEnv-reaches.md`.
  gap-suffices :
      someEnvDef-gap
    → ((g1 g2 g3 g4 g5 : S) → someEnvDef {9} KV.iK (gam' g1 g2 g3 g4 g5))
  gap-suffices gap g1 g2 g3 g4 g5 ya yc b a ar c yaK ycK arK =
    someEnv-gated g1 g2 g3 g4 g5 ya yc b a ar c
      (gap g1 g2 g3 g4 g5 ya yc b a ar c yaK ycK arK) yaK ycK arK

envSetB-to-envHypB2 = Frame.envSetB-to-envHypB2
someEnv-gated      = Frame.someEnv-gated
gap-suffices       = Frame.gap-suffices

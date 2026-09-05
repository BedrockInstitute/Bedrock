{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.534] W3 ONLY: is the collected frame inhabited at KValue's frame?
--
-- The brief names the witness as the widest unmeasured term, and says to
-- build it FIRST if possible.  This file holds the record and the witness
-- and NOTHING else.  The conflict section is added only after this lands.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber,
-- set on the pane by the program and untouched here.  Nothing lands in src/.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-534.runs.W3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; IsOrd; Lset; isTransV; Lset-layer; layer-trans )
open import L.Axioms.Basic {ℓ} using ( LsetS; finSet )
open import L.Axioms.Numerals {ℓ} using ( numeralL )
open import L.Coding.EnvSet {ℓ} lem using ( module Generic )
open import L.Coding.EnvSupply {ℓ} lem
  using ( module SupplyEnv; module SupplyMerge )
open import L.Condensation {ℓ} lem using ( module KValue )
open import Cubical.Data.Nat using ( ℕ; _+_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; ∅ )
open InfinitySet {ℓ} using ( #_; sucV; ω )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

-- =====================================================================
-- THE K SLOT, at TFacts's own index convention.
-- `TFacts`'s K parameter lives in `Fin (5 + n)` and every field reads it
-- through six `suc`s over a `S ^ (11 + n)`
-- (src/L/Condensation/TwelveAgree.lagda.md:129-133).
-- =====================================================================

Kslot : {n : ℕ} → Fin (5 + n) → Vec S (11 + n) → S
Kslot K γ = lookup (suc (suc (suc (suc (suc (suc K)))))) γ

-- =====================================================================
-- THE COLLECTED FRAME.
--
-- Every field is an extra hypothesis some honest form of
-- `src/L/Coding/EnvSupply.lagda.md` takes and the matching `TFacts`
-- field does not carry.  Each is cited at its own line.
-- =====================================================================

record HonestFrame {n : ℕ} (A K : Fin (5 + n)) (γ : Vec S (11 + n))
  : Type (ℓ-suc ℓ) where
  field
    -- `module Fact`'s own telescope (EnvSupply.lagda.md:450).
    Ktr : isTransV (fst (Kslot K γ))
    -- `Fact.valK` (:462), `valK-un` (:471) and the seven `subK-*`
    -- (:497, :508, :519, :530, :541, :552, :563) all take the VALUE
    -- TABLE slot's membership.  That slot is `lookup (suc zero) γ`.
    TK : ⟨ fst (lookup (suc zero) γ) ∈ fst (Kslot K γ) ⟩
    -- `Fact.EnvClosure`'s four (EnvSupply.lagda.md:673-677), which is
    -- what `ConsK`'s `envConsK` (:627-629) is built from.
    numK0 : ⟨ # 0 ∈ fst (Kslot K γ) ⟩
    sucK : (a : V ℓ) → ⟨ a ∈ fst (Kslot K γ) ⟩
         → ⟨ sucV a ∈ fst (Kslot K γ) ⟩
    pairK : (a b : V ℓ) → ⟨ a ∈ fst (Kslot K γ) ⟩ → ⟨ b ∈ fst (Kslot K γ) ⟩
          → ⟨ pr a b ∈ fst (Kslot K γ) ⟩
    finSetK : (m : ℕ) (h : Fin m → V ℓ)
            → ((i : Fin m) → ⟨ h i ∈ fst (Kslot K γ) ⟩)
            → ⟨ finSet m h ∈ fst (Kslot K γ) ⟩
    -- `SupplyEnv.envK-gen` (:277-280) and `envInK-gen` (:351-354) take
    -- `lookup bi γ ≡ B₀`.  The rows read their carrier at slot zero
    -- (TwelveAgree.lagda.md:243-248, `bi = suc⁶ zero`), and the frame's
    -- own carrier is `lookup (suc⁶ A) γ`.
    carrier≡ : lookup zero γ ≡ lookup (suc (suc (suc (suc (suc (suc A)))))) γ
    -- `SupplyEnv.envSetK` (:140-143), which is PINNED to `B₀`.  The
    -- record field is generic in `B` (TwelveAgree.lagda.md:428-433).
    envSetK : (ar : S) (m : ℕ) → fst ar ≡ # m
            → ⟨ fst ar ∈ fst (Kslot K γ) ⟩
            → ⟨ fst (Generic.envSetGen (lookup zero γ) ar) ∈ fst (Kslot K γ) ⟩

-- =====================================================================
-- W3.  ONE inhabitant, at KValue's frame.
--
-- The telescope is `KValue`'s (src/L/Condensation.lagda.md:7380-7383)
-- plus `ω∈γ`, which `SupplyEnv` takes at `src/L/Coding/EnvSupply.lagda.md`
-- :111.  `[LJ-1.495]` took the same telescope with `ω∈γ : ⟨ ω ∈ gam ⟩`
-- (agents/tasks/LJ-1-495/Probe495.agda:91); the chapter's own form is
-- `⟨ ω ∈ sucV gam ⟩` and that is the one taken here.
-- =====================================================================

module Frame
  (lam : V ℓ) (ordλ : IsOrd lam)
  (succλ : (d : V ℓ) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ lam ⟩)
  (gam : V ℓ) (ordγ : IsOrd gam) (γ∈λ : ⟨ gam ∈ lam ⟩)
  (ω∈γ : ⟨ ω ∈ sucV gam ⟩) where

  open KValue lam ordλ succλ ∅∈λ gam ordγ γ∈λ
  module SE = SupplyEnv lam ordλ succλ ∅∈λ gam ordγ γ∈λ ω∈γ
  module SM = SupplyMerge lam ordλ succλ ∅∈λ

  -- The six free conses `[LJ-1.495]` left open (Probe495.agda:166-169).
  -- Slot zero is the rows' carrier and takes `B₀`; slot one is the value
  -- table and takes a member of the level.  The other four are unread.
  z0 : S
  z0 = numeralL 0

  γ₆ : Vec S 20
  γ₆ = SE.B₀ ∷ z0 ∷ z0 ∷ z0 ∷ z0 ∷ z0 ∷ Kenv

  honest-frame-inhabited : HonestFrame {n = 9} iA iK γ₆
  honest-frame-inhabited = record
    { Ktr = layer-trans (Lset-layer lam)
    ; TK = SE.B.num∈λ 0
    ; numK0 = SE.#∈λ 0
    ; sucK = SE.sucK
    ; pairK = SE.B.pr∈λ
    ; finSetK = SM.finSetK
    ; carrier≡ = refl
    ; envSetK = SE.envSetK }

honest-frame-inhabited = Frame.honest-frame-inhabited

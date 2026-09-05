{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.534] W3, RUN 1.  Same record and same witness as runs/W3.agda.wall.txt.
-- ONE variable changed: the two module APPLICATIONS
--   module SE = SupplyEnv lam ... ω∈γ
--   module SM = SupplyMerge lam ordλ succλ ∅∈λ
-- are gone, and every use is a QUALIFIED application instead.  [LJ-1.62]
-- and [LJ-1.158] measured that a module telescope is prepended to the
-- STORED TYPE of every definition in the module, so an application inside
-- an eight-parameter telescope re-elaborates all of them.
-- `module KV = KValue ...` stays: it is eighteen definitions and
-- [LJ-1.507] and [LJ-1.504] both carried it green.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber,
-- set on the pane by the program and untouched here.  Nothing lands in src/.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-534.runs.W3b {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL-trans; IsOrd; Lset; isTransV; Lset-layer; layer-trans )
open import L.Axioms.Basic {ℓ} using ( LsetS; isL-Lset; finSet )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )
open import L.Coding.Model {ℓ} using ( prʟ-fst )
open import L.Coding.EnvSet {ℓ} lem using ( module Generic )
open import L.Coding.EnvSupply {ℓ} lem
  using ( module SupplyEnv; module SupplyMerge )
open import L.Condensation {ℓ} lem using ( module KValue; module KFactsNS )
open import Cubical.Data.Nat using ( ℕ; _+_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; ∅ )
open InfinitySet {ℓ} using ( #_; sucV; ω )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

Kslot : {n : ℕ} → Fin (5 + n) → Vec S (11 + n) → S
Kslot K γ = lookup (suc (suc (suc (suc (suc (suc K)))))) γ

record HonestFrame {n : ℕ} (A K : Fin (5 + n)) (γ : Vec S (11 + n))
  : Type (ℓ-suc ℓ) where
  field
    Ktr : isTransV (fst (Kslot K γ))
    TK : ⟨ fst (lookup (suc zero) γ) ∈ fst (Kslot K γ) ⟩
    numK0 : ⟨ # 0 ∈ fst (Kslot K γ) ⟩
    sucK : (a : V ℓ) → ⟨ a ∈ fst (Kslot K γ) ⟩
         → ⟨ sucV a ∈ fst (Kslot K γ) ⟩
    pairK : (a b : V ℓ) → ⟨ a ∈ fst (Kslot K γ) ⟩ → ⟨ b ∈ fst (Kslot K γ) ⟩
          → ⟨ pr a b ∈ fst (Kslot K γ) ⟩
    finSetK : (m : ℕ) (h : Fin m → V ℓ)
            → ((i : Fin m) → ⟨ h i ∈ fst (Kslot K γ) ⟩)
            → ⟨ finSet m h ∈ fst (Kslot K γ) ⟩
    carrier≡ : lookup zero γ ≡ lookup (suc (suc (suc (suc (suc (suc A)))))) γ
    envSetK : (ar : S) (m : ℕ) → fst ar ≡ # m
            → ⟨ fst ar ∈ fst (Kslot K γ) ⟩
            → ⟨ fst (Generic.envSetGen (lookup zero γ) ar) ∈ fst (Kslot K γ) ⟩

module Frame
  (lam : V ℓ) (ordλ : IsOrd lam)
  (succλ : (d : V ℓ) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ lam ⟩)
  (gam : V ℓ) (ordγ : IsOrd gam) (γ∈λ : ⟨ gam ∈ lam ⟩)
  (ω∈γ : ⟨ ω ∈ sucV gam ⟩) where

  module KV = KValue lam ordλ succλ ∅∈λ gam ordγ γ∈λ

  open KFactsNS.KFacts KV.facts using ()
    renaming ( numK0 to kNumK0 ; pairK to kPairK )

  -- SupplyEnv's own carrier, written out.  `SupplyEnv.B₀` is
  -- `LsetS gam ordγ` (src/L/Coding/EnvSupply.lagda.md:124-125), so the
  -- two are the same term and no coercion is needed.
  B₀ : S
  B₀ = LsetS gam ordγ

  z0 : S
  z0 = numeralL 0

  γ₆ : Vec S 20
  γ₆ = B₀ ∷ z0 ∷ z0 ∷ z0 ∷ z0 ∷ z0 ∷ KV.Kenv

  -- The V-level pair closure, from KFacts's own S-level `pairK`.
  pairK-V : (a b : V ℓ) → ⟨ a ∈ Lset lam ⟩ → ⟨ b ∈ Lset lam ⟩
          → ⟨ pr a b ∈ Lset lam ⟩
  pairK-V a b ha hb =
    subst (λ w → ⟨ w ∈ Lset lam ⟩) (prʟ-fst aS bS) (kPairK aS bS ha hb)
    where
    aS : S
    aS = a , isL-trans {x = Lset lam} {y = a} ha (isL-Lset lam ordλ)
    bS : S
    bS = b , isL-trans {x = Lset lam} {y = b} hb (isL-Lset lam ordλ)

  honest-frame-inhabited : HonestFrame {n = 9} KV.iA KV.iK γ₆
  honest-frame-inhabited = record
    { Ktr = layer-trans (Lset-layer lam)
    ; TK = kNumK0
    ; numK0 = subst (λ w → ⟨ w ∈ Lset lam ⟩) (numeralL-fst 0) kNumK0
    ; sucK = SupplyEnv.sucK lam ordλ succλ ∅∈λ gam ordγ γ∈λ ω∈γ
    ; pairK = pairK-V
    ; finSetK = SupplyMerge.finSetK lam ordλ succλ ∅∈λ
    ; carrier≡ = refl
    ; envSetK = SupplyEnv.envSetK lam ordλ succλ ∅∈λ gam ordγ γ∈λ ω∈γ }

honest-frame-inhabited = Frame.honest-frame-inhabited

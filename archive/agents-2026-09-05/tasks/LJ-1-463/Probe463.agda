{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.463] W3 first, then the obligation someEnv-at-K.
-- Layout from [LJ-1.457] Probe457.agda:52-55 and :74-75, not from
-- that brief. n = 9: iK' : Fin 14, Kenv' : S ^ 20, KValue's fourteen
-- slots at positions 6 to 19. W3 is W3.env-in-K. The obligation
-- someEnv-at-K names the type; W3 shows the membership half does
-- not close from KFacts.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide
-- caliber, set on the pane by the program and untouched here.
-- Nothing lands in src/.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-463.Probe463 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd )
open import L.Axioms.Numerals {ℓ} using ( numeralL )
open import L.Condensation {ℓ} lem using ( module KValue; module KFactsNS )
open import L.Condensation.LowerAgree {ℓ} lem using ( someEnvDef )
open import L.Coding.EnvSet {ℓ} lem using ( module Generic )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; ∅ )
open InfinitySet using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ
open KFactsNS

-- =====================================================================
-- D-10.  n = 9 is the arity someEnvDef needs.
--   someEnvDef {n}: K : Fin (5 + n), γ : S ^ (11 + n)
--                  (LowerAgree.lagda.md:52-53).
--   [LJ-1.457]:     iK' : Fin (5 + 9), Kenv' : Vec S (11 + 9)
--                  (Probe457.agda:52-55, :74-75).
--   They meet.  Lookup suc^6 iK' on Kenv' is lookup iK on Kenv.
-- =====================================================================

module W3
  (lam : V ℓ) (ordλ : IsOrd lam)
  (succλ : (d : V ℓ) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ lam ⟩)
  (gam : V ℓ) (ordγ : IsOrd gam) (γ∈λ : ⟨ gam ∈ lam ⟩) where

  open KValue lam ordλ succλ ∅∈λ gam ordγ γ∈λ

  -- Six dummy fillers, copied from Probe457.agda:52-55.
  Kenv' : Vec S (11 + 9)
  Kenv' = numeralL 0 ∷ numeralL 0 ∷ numeralL 0
        ∷ numeralL 0 ∷ numeralL 0 ∷ numeralL 0
        ∷ Kenv

  iK' : Fin (5 + 9)
  iK' = iK

  bound : S
  bound = lookup (suc (suc (suc (suc (suc (suc iK')))))) Kenv'

  -- W3. Membership of THE environment set the construction builds,
  -- without the satisfaction half. E is Generic.envSetGen at the
  -- B slot envHypB2 reads (slot 0 of Kenv', the first filler).
  -- Membership is the unmeasured term: KFacts supplies numK and
  -- pairK, not envSetK (Condensation.lagda.md:7413-7425).
  env-in-K : (ya yc ar : S)
           → ⟨ fst ya ∈ fst bound ⟩
           → ⟨ fst yc ∈ fst bound ⟩
           → ⟨ fst ar ∈ fst bound ⟩
           → Σ S (λ E → ⟨ fst E ∈ fst bound ⟩)
  env-in-K ya yc ar yaK ycK arK = E , EK
    where
    B : S
    B = lookup zero Kenv'
    module G = Generic B ar
    E : S
    E = G.envSetGen
    -- Attempt: the bound's delivered numeral membership. If this
    -- typechecks, envSetGen equals numeralL 0 definitionally. If
    -- Agda refuses, the closure facts do not put the environment
    -- set in K.
    EK : ⟨ fst E ∈ fst bound ⟩
    EK = KFacts.numK0 facts

-- =====================================================================
-- THE OBLIGATION.  The type forms at n = 9: iK' : Fin (5 + 9) and
-- Kenv' : Vec S (11 + 9).  W3.env-in-K does not inhabit the membership
-- half (runs/w3-1.out, [UnequalTerms] fst (numeralL 0) != fst envSetGen).
-- Satisfaction is unreachable.  No body.
-- =====================================================================

iK' : Fin (5 + 9)
iK' = suc zero

Kenv' :
    (lam : V ℓ) (ordλ : IsOrd lam)
    (succλ : (d : V ℓ) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩)
    (∅∈λ : ⟨ ∅ ∈ lam ⟩)
    (gam : V ℓ) (ordγ : IsOrd gam) (γ∈λ : ⟨ gam ∈ lam ⟩)
  → Vec S (11 + 9)
Kenv' = W3.Kenv'

someEnv-at-K :
    (lam : V ℓ) (ordλ : IsOrd lam)
    (succλ : (d : V ℓ) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩)
    (∅∈λ : ⟨ ∅ ∈ lam ⟩)
    (gam : V ℓ) (ordγ : IsOrd gam) (γ∈λ : ⟨ gam ∈ lam ⟩)
  → someEnvDef {9} iK' (Kenv' lam ordλ succλ ∅∈λ gam ordγ γ∈λ)
someEnv-at-K = {!!}

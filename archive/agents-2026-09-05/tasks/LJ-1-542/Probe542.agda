{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.542] The TWELVE numK rows of TFacts, at KValue's frame.
--
-- W3 FIRST, and alone: ONE numeral, `numK7`, read off [LJ-1.495]'s
-- shifted KFacts at TFacts's own index.  If it goes through with no
-- `KFactsCons` and no conversion, the family costs NOTHING and the
-- telescope of "extra hypotheses" the brief asks for is EMPTY.
--
-- WHY THIS IS THE DECISIVE MINIATURE.  `KFacts.numK7`
-- (src/L/Condensation.lagda.md:6101) is
--   ⟨ fst (numeralL 7) ∈ fst (lookup K γ) ⟩
-- and `TFacts.numK7` (src/L/Condensation/TwelveAgree.lagda.md:152) is
--   ⟨ fst (numeralL 7) ∈ fst (lookup (suc^6 K) γ') ⟩ .
-- `lookup (suc i) (x ∷ xs)` reduces to `lookup i xs` definitionally, so
-- at γ' = c6 ∷ c5 ∷ c4 ∷ c3 ∷ c2 ∷ c1 ∷ Kenv the two types should be the
-- SAME type, not two types joined by a transport.  This file asks Agda.
--
-- [LJ-1.539] already made the same bet on ONE field and won it:
-- `facts .arityK` is passed at the SHIFTED index with no conversion
-- (agents/tasks/LJ-1-539/Probe539.agda:375, and the comment at :349-354
-- that says the file stops checking if the reduction stops being
-- definitional).  AGENTS.md:45 forbids carrying that cure by analogy, so
-- this file re-measures it on the numK rows at their own site.
--
-- I do NOT rebuild [LJ-1.495]'s shift.  `KFactsCons` is not imported.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber,
-- set on the pane by the program and untouched here.  Nothing lands in
-- src/.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-542.Probe542 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )
open import L.Condensation {ℓ} lem using ( module KValue; module KFactsNS )
open import L.Coding.Bound {ℓ} lem using ( module Bound )
open import L.Coding.EnvSupply {ℓ} lem using ( module SupplyEnv )
open import Cubical.Data.Nat using ( ℕ; _+_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; ∅ )
open InfinitySet {ℓ} using ( sucV; ω; #_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ
open KFactsNS
open KFacts

-- =====================================================================
-- W3.  ONE numeral, at the shifted index, from `KValue.facts` alone.
-- =====================================================================

module W3
  (lam : V ℓ) (ordλ : IsOrd lam)
  (succλ : (d : V ℓ) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ lam ⟩)
  (gam : V ℓ) (ordγ : IsOrd gam) (γ∈λ : ⟨ gam ∈ lam ⟩) where

  open KValue lam ordλ succλ ∅∈λ gam ordγ γ∈λ

  -- `KValue`'s seven parameters, and nothing else.  No `ω∈σ`, no
  -- `SupplyEnv`, no cons.
  numK7-at-shift : (c1 c2 c3 c4 c5 c6 : S)
    → ⟨ fst (numeralL 7)
        ∈ fst (lookup (suc (suc (suc (suc (suc (suc iK))))))
                 (c6 ∷ c5 ∷ c4 ∷ c3 ∷ c2 ∷ c1 ∷ Kenv)) ⟩
  numK7-at-shift c1 c2 c3 c4 c5 c6 = facts .numK7

numK7-at-shift = W3.numK7-at-shift

-- =====================================================================
-- W2.  THE TWELVE, ONCE, AT `TFacts`'s OWN INDICES.
--
--   `TFacts.numK0` to `numK11`
--   (src/L/Condensation/TwelveAgree.lagda.md:145-156), copied verbatim.
--   The twelve name only `K` and `γ'` of that record's fifteen index
--   parameters, so only those two are stated here.  Instantiated below
--   at n = 9 against `KValue`'s `Fin 14`, which is the frame
--   [LJ-1.495] measured (agents/tasks/LJ-1-495/lj-1.495-report.md:56-60).
--
--   The other twenty nine TFacts fields are NOT here.  AD12 gives this
--   task one obligation and the brief forbids collecting another family.
-- =====================================================================

record NumKTwelve {n : ℕ} (K : Fin (5 + n)) (γ' : Vec S (11 + n))
  : Type (ℓ-suc ℓ) where
  field
    numK0 : ⟨ fst (numeralL 0) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
    numK1 : ⟨ fst (numeralL 1) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
    numK2 : ⟨ fst (numeralL 2) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
    numK3 : ⟨ fst (numeralL 3) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
    numK4 : ⟨ fst (numeralL 4) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
    numK5 : ⟨ fst (numeralL 5) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
    numK6 : ⟨ fst (numeralL 6) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
    numK7 : ⟨ fst (numeralL 7) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
    numK8 : ⟨ fst (numeralL 8) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
    numK9 : ⟨ fst (numeralL 9) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
    numK10 : ⟨ fst (numeralL 10) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
    numK11 : ⟨ fst (numeralL 11) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩

-- =====================================================================
-- THE OBLIGATION, AT `KValue`'s FRAME.
--
-- `KValue` (src/L/Condensation.lagda.md:7380-7383) binds the carrier and
-- the stage and supplies ONE `KFacts` value, `facts` (:7411), over
-- `Kenv : S ^ 14` (:7389).  Six cons cells put it at `TFacts`'s lengths:
-- `S ^ 20` is `S ^ (11 + 9)` and `Fin 14` is `Fin (5 + 9)`.
--
-- THE TELESCOPE OF EXTRA HYPOTHESES IS EMPTY, AND THAT IS THE RESULT.
-- W3 above measured that `facts .numK7` already inhabits the shifted
-- index.  So the twelve take NO extra hypothesis: not `SupplyEnv`'s
-- eighth parameter `ω∈σ` (src/L/Coding/EnvSupply.lagda.md:111), which
-- [LJ-1.538] had to carry, and not a slot-one fact, which [LJ-1.539]
-- had to carry (agents/tasks/LJ-1-539/Probe539.agda:368-371).  The term
-- below takes `KValue`'s seven parameters, the six free cells, and
-- nothing else.
--
-- THE SIX CELLS STAY FREE, as in [LJ-1.539] and unlike [LJ-1.538].
-- [LJ-1.538] pinned cell 0 to `SupplyEnv.B₀` because the nine env forms
-- read the carrier out of it (agents/tasks/LJ-1-538/Probe538.agda
-- :177-178).  THE TWELVE READ NO CELL BUT `K`, so this frame pins
-- nothing.
--
-- I DO NOT REBUILD [LJ-1.495]'s SHIFT.  `KFactsCons` is not imported and
-- `six` is not rewritten.  The reduction `lookup (suc i) (x ∷ xs) ↝
-- lookup i xs` does the whole shift for these twelve fields, which is a
-- strictly cheaper fact than the one [LJ-1.495] proved: its `six`
-- REBUILDS the record so that the twenty six can be read at the shifted
-- indices AS A RECORD (agents/tasks/LJ-1-495/Probe495.agda:166-199).
-- For the twelve taken FIELD BY FIELD no rebuild is needed at all.
-- =====================================================================

module Frame
  (lam : V ℓ) (ordλ : IsOrd lam)
  (succλ : (d : V ℓ) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ lam ⟩)
  (gam : V ℓ) (ordγ : IsOrd gam) (γ∈λ : ⟨ gam ∈ lam ⟩) where

  open KValue lam ordλ succλ ∅∈λ gam ordγ γ∈λ

  γ★ : (c1 c2 c3 c4 c5 c6 : S) → Vec S 20
  γ★ c1 c2 c3 c4 c5 c6 = c6 ∷ c5 ∷ c4 ∷ c3 ∷ c2 ∷ c1 ∷ Kenv

  numK-frame-inhabited : (c1 c2 c3 c4 c5 c6 : S)
                       → NumKTwelve {n = 9} iK (γ★ c1 c2 c3 c4 c5 c6)
  numK-frame-inhabited c1 c2 c3 c4 c5 c6 = record
    { numK0 = facts .numK0 ; numK1 = facts .numK1
    ; numK2 = facts .numK2 ; numK3 = facts .numK3
    ; numK4 = facts .numK4 ; numK5 = facts .numK5
    ; numK6 = facts .numK6 ; numK7 = facts .numK7
    ; numK8 = facts .numK8 ; numK9 = facts .numK9
    ; numK10 = facts .numK10 ; numK11 = facts .numK11 }

-- THE OBLIGATION AT THE TOP LEVEL: KValue's seven, then the six free
-- cells, then the witness.  No hypothesis sits between them.
numK-frame-inhabited = Frame.numK-frame-inhabited

-- =====================================================================
-- SHIFT OR FORM.  THE BRIEF NAMES A SECOND ROUTE, SO IT IS MEASURED
-- HERE AND NOT ARGUED.
--
-- The brief's route is `SupplyEnv.#∈λ`
-- (src/L/Coding/EnvSupply.lagda.md:229), transported by `numeralL-fst`
-- (src/L/Axioms/Numerals.lagda.md:179).  Two facts about it, both read
-- off the tree:
--
--   1. `#∈λ` is DERIVED FROM `Bound.num∈λ`, not the other way round.
--      `#∈λ n = subst _ (numeralL-fst n) (B.num∈λ n)`
--      (src/L/Coding/EnvSupply.lagda.md:230).  So reaching the record's
--      `numK` through `#∈λ` transports OUT across `numeralL-fst` and
--      then straight back IN across its `sym`.  It is a round trip.
--   2. `#∈λ` lives in `SupplyEnv`, whose telescope carries an EIGHTH
--      parameter `ω∈γ : ⟨ ω ∈ sucV gam ⟩`
--      (src/L/Coding/EnvSupply.lagda.md:111) that `KValue`'s seven do
--      not have.  [LJ-1.538] had to carry it
--      (agents/tasks/LJ-1-538/Probe538.agda:164).  The twelve do not
--      consume it, so on the form route it is carried and never used:
--      exactly the trim [LJ-1.538] reported at its own site.
--
-- Both rival routes below are built to the SAME record `NumKTwelve` at
-- the SAME frame, so the three prices are like for like.
-- =====================================================================

module Form
  (lam : V ℓ) (ordλ : IsOrd lam)
  (succλ : (d : V ℓ) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ lam ⟩)
  (gam : V ℓ) (ordγ : IsOrd gam) (γ∈λ : ⟨ gam ∈ lam ⟩)
  (ω∈σ : ⟨ ω ∈ sucV gam ⟩) where

  module KV = KValue lam ordλ succλ ∅∈λ gam ordγ γ∈λ
  module SE = SupplyEnv lam ordλ succλ ∅∈λ gam ordγ γ∈λ ω∈σ
  module B  = Bound lam ordλ succλ ∅∈λ

  γ★ : (c1 c2 c3 c4 c5 c6 : S) → Vec S 20
  γ★ c1 c2 c3 c4 c5 c6 = c6 ∷ c5 ∷ c4 ∷ c3 ∷ c2 ∷ c1 ∷ KV.Kenv

  -- ROUTE `#∈λ`, one numeral, generic in `k`.  The subst is the round
  -- trip named above.
  numK-by-form : (k : ℕ) (c1 c2 c3 c4 c5 c6 : S)
    → ⟨ fst (numeralL k)
        ∈ fst (lookup (suc (suc (suc (suc (suc (suc KV.iK))))))
                 (γ★ c1 c2 c3 c4 c5 c6)) ⟩
  numK-by-form k c1 c2 c3 c4 c5 c6 =
    subst (λ w → ⟨ w ∈ fst (lookup (suc (suc (suc (suc (suc (suc KV.iK))))))
                              (γ★ c1 c2 c3 c4 c5 c6)) ⟩)
      (sym (numeralL-fst k)) (SE.#∈λ k)

  -- ROUTE `num∈λ`: `Bound`'s own form, which is what `KValue.facts`
  -- fills these twelve fields with (src/L/Condensation.lagda.md
  -- :7416-7419).  It needs only FOUR of KValue's seven parameters and
  -- no subst at all, so it is the cheapest form route.
  numK-by-bound : (k : ℕ) (c1 c2 c3 c4 c5 c6 : S)
    → ⟨ fst (numeralL k)
        ∈ fst (lookup (suc (suc (suc (suc (suc (suc KV.iK))))))
                 (γ★ c1 c2 c3 c4 c5 c6)) ⟩
  numK-by-bound k c1 c2 c3 c4 c5 c6 = B.num∈λ k

  -- THE WHOLE RECORD BY THE FORM ROUTE, so the comparison with
  -- `numK-frame-inhabited` is like for like.
  numK-frame-by-form : (c1 c2 c3 c4 c5 c6 : S)
                     → NumKTwelve {n = 9} KV.iK (γ★ c1 c2 c3 c4 c5 c6)
  numK-frame-by-form c1 c2 c3 c4 c5 c6 = record
    { numK0 = f 0 ; numK1 = f 1 ; numK2 = f 2 ; numK3 = f 3
    ; numK4 = f 4 ; numK5 = f 5 ; numK6 = f 6 ; numK7 = f 7
    ; numK8 = f 8 ; numK9 = f 9 ; numK10 = f 10 ; numK11 = f 11 }
    where
    f : (k : ℕ) → ⟨ fst (numeralL k)
                    ∈ fst (lookup (suc (suc (suc (suc (suc (suc KV.iK))))))
                             (γ★ c1 c2 c3 c4 c5 c6)) ⟩
    f k = numK-by-form k c1 c2 c3 c4 c5 c6

numK-by-form = Form.numK-by-form
numK-by-bound = Form.numK-by-bound
numK-frame-by-form = Form.numK-frame-by-form

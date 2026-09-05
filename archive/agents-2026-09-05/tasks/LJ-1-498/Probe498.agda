{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.498] PROBE.  Does the level graph name any constant at all.
-- It runs in agents/tasks/LJ-1-498/ and lands nothing in src/.
--
--   STEP ONE, W3 FIRST   the census.  countFo (LsetGraphAt w b),
--                        computed, not read off by eye.  ANSWER: 664.
--   STEP TWO             the decomposition, so the 664 is attributed.
--   STEP THREE           the wall, in one line of Agda, and the
--                        instrument that spends it.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-498.Probe498 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import FOL.Manipulation.Parameters using ( countFo )
open import FOL.Manipulation.Bounding using ( BoundedFo; module Relabel )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; Lset; IsOrd )
open import L.Axioms.Numerals {ℓ} using ( numeralL )
open import L.Hull {ℓ} lem using ( module AtStage )
open import L.Coding.Model {ℓ}
  using ( appAt; domAt; prAtL; tagAtL; tagPairAtL; closedAt
        ; arityTagAtL; arityTagPairAtL )
open import L.Coding.Shape {ℓ} using ( shapedAt; shapes; isTmAt; binForm; unForm; noneB; noneU; zeroPay; bothTm; fstTm )
open import L.Coding.CodeSet {ℓ} lem using ( keyArityAtL; hasWitnessAt )
open import L.Coding.Graph {ℓ} lem using ( satGraphAt )
open import L.Coding.Powerset {ℓ} lem
  using ( isCodeAt; envOneAt; DefinesAt; DefBody; DefAt )
open import L.Coding.Sequence {ℓ} lem using ( LsetGraphAt )
open import L.Coding.Bound {ℓ} lem using ( module Bound )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; module InfinitySet )
open InfinitySet using ( sucV )
open import Cubical.Data.Vec using ( Vec; []; _∷_ )
open import Cubical.Data.Nat using ( _+_; _·_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
module CS = hPropStructure 𝒮ʟ

-- ────────────────────────────────────────────────────────────────────
-- W3.  THE CENSUS.
--
-- countFo counts `con` occurrences and nothing else
-- (src/FOL/Manipulation/Parameters.lagda.md:70-86).  The seal at
-- src/L/Coding/Graph.lagda.md:203 stops the count, so it is opened
-- here; opening it is legal in a probe and costs nothing in src/.
-- ────────────────────────────────────────────────────────────────────

opaque
  unfolding satGraphAt

  -- THE CENSUS.  Green, not an error message: the level graph names
  -- SIX HUNDRED AND SIXTY-FOUR constants, at n, w and b all variable.
  census : {n : ℕ} (w b : Fin n) → countFo (LsetGraphAt w b) ≡ 664
  census w b = refl

  -- Every reachable formula of the level graph, counted.  The fifteen
  -- counts are packed into one numeral, base 100000, least significant
  -- first, because the elaborator prints only the FIRST mismatch of a
  -- vector and this way one run reports all fifteen.
  pack : {m : ℕ} → Vec ℕ m → ℕ
  pack [] = 0
  pack (c ∷ cs) = c + 100000 · pack cs

  tally : {n : ℕ} (w b : Fin n) → Vec ℕ 15
  tally {n} w b
      = countFo (prAtL w b w)                  -- 0  the pair reader
      ∷ countFo (appAt w b w)                  -- 1  table application
      ∷ countFo (domAt w b)                    -- 2  the domain clause
      ∷ countFo (tagAtL w 7 b)                 -- 3  ONE tag
      ∷ countFo (closedAt w)                   -- 4  subformula closure
      ∷ countFo (shapedAt w b)                 -- 5  the twelve shapes
      ∷ countFo (keyArityAtL w 1)              -- 6  arity-1 key
      ∷ countFo (hasWitnessAt w b)             -- 7  closed and shaped witness
      ∷ countFo (isCodeAt w b)                 -- 8  a code at a slot
      ∷ countFo (envOneAt w b)                 -- 9  one-place environment
      ∷ countFo (DefinesAt w b w)              -- 10 the defines clause
      ∷ countFo (satGraphAt w b w)             -- 11 sealed satisfaction graph
      ∷ countFo (DefBody b)                    -- 12 code, graph, defines
      ∷ countFo (DefAt w b)                    -- 13 the definable power
      ∷ countFo (LsetGraphAt w b)              -- 14 THE LEVEL GRAPH
      ∷ []

  -- MEASURED, runs/w3-3.out:4.  Decoded in the report's census table.
  --   0,0,0,1,8,26,1,34,35,2,4,44,83,166,664
  -- and the arithmetic closes: 34 = 8+26, 35 = 1+34, 83 = 35+44+4,
  -- 166 = 2*83, 664 = 4*166.  Nothing is unattributed.
  readout : {n : ℕ} (w b : Fin n) → pack (tally w b)
          ≡ 6640016600083000440000400002000350003400001000260000800001000000000000000
  readout w b = refl

  -- The shape layer, so shapedAt's 26 closes against its own parts.
  tally2 : {n : ℕ} (A : Fin n) → Vec ℕ 6
  tally2 {n} A
      = countFo (isTmAt A A A)              -- 0
      ∷ countFo (binForm 7 (noneB {n = n})) -- 1
      ∷ countFo (unForm 7 (noneU {n = n}))  -- 2
      ∷ countFo (bothTm A)                  -- 3
      ∷ countFo (zeroPay {n = n})           -- 4
      ∷ countFo (shapes A)                  -- 5
      ∷ []

  -- MEASURED, runs/w3-4.out:4.  isTmAt 2, binForm 1, unForm 1,
  -- bothTm 4, zeroPay 1, shapes 26; and 26 = 12 form tags + 8 (bothTm
  -- twice) + 4 (fstTm twice) + 2 (zeroPay twice).
  readout2 : {n : ℕ} (A : Fin n) → pack (tally2 A)
           ≡ 260000100004000010000100002
  readout2 A = refl

-- ────────────────────────────────────────────────────────────────────
-- STEP THREE.  THE WALL, AND THE INSTRUMENT.
--
-- The census is NOT empty, so `mapFo` is the wrong instrument: it wants
-- a TOTAL map CS.S → SL and the brief is right that none can exist.
-- The tree's instrument for a PARTIAL one is Relabel
-- (src/FOL/Manipulation/Bounding.lagda.md:146), whose own prose names
-- this very instance at :130-134: "the source is the model's carrier,
-- the target is a stage's member type, the world is the hierarchy".
-- ────────────────────────────────────────────────────────────────────

module StageWorld (α : S) (ordα : IsOrd α) where

  module ASt = AtStage α ordα
  open ASt using ( SL )

  -- the predicate the certificate is about: a constant of the model
  -- lies in THIS stage.  P is exactly SL's second component.
  P : CS.S → Type (ℓ-suc ℓ)
  P c = ⟨ fst c ∈ˢ Lset α ⟩

  module ToStage = Relabel {K = CS.S} {K' = SL} {W = S}
    fst fst P (λ c p → fst c , p) (λ c p → refl)

  -- THE WALL, in one line of Agda.  664 leaves, one per constant.
  Wall : {n : ℕ} → Fin n → Fin n → Type (ℓ-suc ℓ)
  Wall w b = BoundedFo P (LsetGraphAt w b)

  -- and the obligation, discharged the moment the wall is.
  graphFo-at-SL-given : {n : ℕ} (w b : Fin n) → Wall w b → Formula SL n
  graphFo-at-SL-given w b cert = ToStage.liftFo (LsetGraphAt w b) cert

  -- Every one of the 664 constants enters through tagAtL
  -- (src/L/Coding/Model.lagda.md:586), and it is `numeralL k`.  So the
  -- leaf of the certificate is one line, and the whole wall reduces to
  -- the stage condition on numerals.
  bd-tagAtL : {n : ℕ} (s : Fin n) (k : ℕ) (x : Fin n)
            → P (numeralL k) → BoundedFo P (tagAtL s k x)
  bd-tagAtL s k x h = (_ , h) , _

  -- and the same one line carries every composite that the census
  -- attributed to a tag.  NUM is the stage condition on numerals: the
  -- whole 664-leaf wall is built from it and from nothing else.
  NUM : Type (ℓ-suc ℓ)
  NUM = (k : ℕ) → P (numeralL k)

  bd-tagPairAtL : {n : ℕ} (s : Fin n) (k : ℕ) (a b : Fin n)
                → P (numeralL k) → BoundedFo P (tagPairAtL s k a b)
  bd-tagPairAtL s k a b h = _ , ((_ , h) , _)

  bd-arityTagAtL : {n : ℕ} (c ar : Fin n) (k : ℕ) (a : Fin n)
                 → P (numeralL k) → BoundedFo P (arityTagAtL c ar k a)
  bd-arityTagAtL c ar k a h = _ , ((_ , h) , _)

  bd-arityTagPairAtL : {n : ℕ} (c ar : Fin n) (k : ℕ) (a b : Fin n)
                     → P (numeralL k)
                     → BoundedFo P (arityTagPairAtL c ar k a b)
  bd-arityTagPairAtL c ar k a b h = _ , (_ , ((_ , h) , _))

  -- THE PUBLIC HALF OF THE WALL, DISCHARGED.  Eight leaves, tags
  -- 2,3,4,5,8,9,10,11 (src/L/Coding/Model.lagda.md:2182-2189).  The
  -- relation payloads carry no constant, so each is solved by eta.
  -- binShapeAt/unShapeAt take the payload as an ARGUMENT, and BoundedFo
  -- pattern matches on the formula, so a lemma stated at a variable
  -- payload leaves an uninvertible metavariable: the tuple is written
  -- at the composite instead, where the payload is concrete.
  bd-closedAt : {n : ℕ} → NUM → (C : Fin n) → BoundedFo P (closedAt C)
  bd-closedAt hyp C =
      (_ , ((_ , (_ , ((_ , hyp 2) , _))) , _))
    , ( (_ , ((_ , (_ , ((_ , hyp 3) , _))) , _))
    , ( (_ , ((_ , (_ , ((_ , hyp 4) , _))) , _))
    , ( (_ , ((_ , ((_ , hyp 5) , _)) , _))
    , ( (_ , ((_ , ((_ , hyp 8) , _)) , _))
    , ( (_ , ((_ , ((_ , hyp 9) , _)) , _))
    , ( (_ , ((_ , (_ , ((_ , hyp 10) , _))) , _))
      , (_ , ((_ , (_ , ((_ , hyp 11) , _))) , _)) ))))))

-- ────────────────────────────────────────────────────────────────────
-- STEP FOUR.  THE HYPOTHESIS IS NOT A HYPOTHESIS AT A LIMIT.
--
-- NUM is what the whole 664-leaf wall reduces to, and src/ already
-- proves it at any limit stage: `num∈λ`, src/L/Coding/Bound.lagda.md:139.
-- So the certificate has a supplier and the wall is not one.
-- ────────────────────────────────────────────────────────────────────

module LimitStage (lam : S) (ordλ : IsOrd lam)
                  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
                  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  module SW = StageWorld lam ordλ
  module B  = Bound lam ordλ succλ ∅∈λ

  -- THE SUPPLY.  No new hypothesis: the tree's own fact, at the type
  -- the certificate wants.
  num : SW.NUM
  num = B.num∈λ

  -- and the eight leaves of closedAt are then unconditional here.
  closed-cert : {n : ℕ} (C : Fin n) → BoundedFo SW.P (closedAt C)
  closed-cert C = SW.bd-closedAt num C

{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.505] The environment vector `γ'` at KValue's frame.
--
-- ONE obligation (AD12): `gammaPrime : S ^ (11 + 9)`, the vector a
-- `TFacts` value at KValue's frame would be stated over.  Nothing
-- lands in src/.  NO `TFacts` value is built.
--
-- THE FRAME, MEASURED BEFORE ANY AGDA (D-10).
--   `TFacts` is over `γ' : S ^ (11 + n)` with its fifteen indices in
--   `Fin (5 + n)`, and EVERY field reaches them through six `suc`s
--   (src/L/Condensation/TwelveAgree.lagda.md:131-133).  So the
--   `Fin (5 + n)` region is γ' slots 6 .. 5+(5+n), the whole tail, and
--   the six front slots are all that is left.  At n = 9 the tail is 14
--   slots, which is exactly `KValue.Kenv : S ^ 14`
--   (src/L/Condensation.lagda.md:7389-7395), so 6 + 14 = 11 + 9.
--   `lengthCheck` below is W3 and settles that arithmetic alone.
--
--   The six front slots are NOT free-floating.  `TFacts`'s consumer
--   states `γ'` as `f ∷ e ∷ d ∷ γ` with `γ : S ^ (8 + n)`
--   (src/L/Condensation.lagda.md:6971), so slots 0,1,2 are the three
--   existential witnesses of `satGraphOn` (src/L/Coding/Graph.lagda.md
--   :104-111) and slots 3,4,5 are the outer environment's own front.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide
-- caliber, set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-505.Probe505 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd )
open import FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ʟ using ( _^_ )
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import L.Axioms.Numerals {ℓ} using ( numeralL )
open import L.Coding.EnvSupply {ℓ} lem using ( module SupplyEnv )
open import L.Condensation {ℓ} lem using ( module KValue )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; ∅ )
open InfinitySet {ℓ} using ( sucV; ω )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

-- =====================================================================
-- W3.  THE LENGTH ALONE, at junk in every front slot.
--   If `11 + 9` and `6 + 14` do not agree definitionally here, the
--   arithmetic is the finding and nothing else in this task matters.
-- =====================================================================

module W3 (lam : V ℓ) (ordλ : IsOrd lam)
  (succλ : (d : V ℓ) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ lam ⟩)
  (gam : V ℓ) (ordγ : IsOrd gam) (γ∈λ : ⟨ gam ∈ lam ⟩) where

  module KV = KValue lam ordλ succλ ∅∈λ gam ordγ γ∈λ

  -- the six front slots, appended to Kenv, at the length the record demands
  lengthCheck : (j : S) → S ^ (11 + 9)
  lengthCheck j = j ∷ j ∷ j ∷ j ∷ j ∷ j ∷ KV.Kenv

-- =====================================================================
-- THE VECTOR.
--
-- The telescope is `SupplyEnv`'s, not `KValue`'s.  `[LJ-1.503]`
-- settled the gate at the weakest sufficient form `⟨ ω ∈ sucV gam ⟩`
-- (src/L/Coding/EnvSupply.lagda.md:111) and the mathematician ruled a
-- `TFacts` value carries it, so slot 0 can be stated as the object
-- `SupplyEnv` itself delivers rather than as a copy of its definition.
-- =====================================================================

module Frame (lam : V ℓ) (ordλ : IsOrd lam)
  (succλ : (d : V ℓ) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ lam ⟩)
  (gam : V ℓ) (ordγ : IsOrd gam) (γ∈λ : ⟨ gam ∈ lam ⟩)
  (ω∈σ : ⟨ ω ∈ sucV gam ⟩) where

  module KV = KValue lam ordλ succλ ∅∈λ gam ordγ γ∈λ
  module SE = SupplyEnv lam ordλ succλ ∅∈λ gam ordγ γ∈λ ω∈σ

  -- THE JUNK VALUE, named once so the vector reads honestly.
  -- `numeralL 0` and no other: it is a closed named object that this
  -- frame ALREADY holds (Kenv slot 2, src/L/Condensation.lagda.md
  -- :7390), so it adds no import and no new elaboration, and every
  -- slot that carries it below is carrying it because the census found
  -- NOTHING that names that slot.  It is not a claim about the slot.
  junk : S
  junk = numeralL 0

  -- ===================================================================
  -- THE OBLIGATION.
  --
  --   slot 0   SE.B₀, the carrier.  Nine fields name it: the five
  --            `envK-*` and the four `envInK-*`, each through its own
  --            prefix (TwelveAgree.lagda.md:186, :192, :198, :204,
  --            :210, :216, :223, :230, :237).  `[LJ-1.499]` fixed it
  --            (agents/tasks/LJ-1-499/Probe499.agda:83-84).
  --   slot 1   UNCONSTRAINED AS AN OBJECT.  Nine fields name the slot
  --            and every one of them names a ROLE: the satisfaction
  --            graph `T`.  No named graph object exists in the tree.
  --   slot 2   UNCONSTRAINED AS AN OBJECT.  Four fields name the slot,
  --            all in the role of the code set `C`.
  --   slots 3,4,5  UNCONSTRAINED.  ZERO references, at any prefix
  --            depth, in all 59 fields.
  --   slots 6..19  KValue.Kenv, whole and in order.
  -- ===================================================================

  gammaPrime : S ^ (11 + 9)
  gammaPrime = SE.B₀ ∷ junk ∷ junk ∷ junk ∷ junk ∷ junk ∷ KV.Kenv

  -- ===================================================================
  -- EVERY NAMED SLOT, CHECKED WHERE THE RECORD READS IT.
  --   Each `refl` is at the S level, which is stronger than the `fst`
  --   equation the corresponding field states.
  -- ===================================================================

  -- Slot 0, at the index `envK-*` and `envInK-*` reach.
  slot0-is-carrier : lookup zero gammaPrime ≡ SE.B₀
  slot0-is-carrier = refl

  -- SLOT 0 IS NOT A CONVENIENCE, IT IS PINNED.  `witK`'s first clause
  -- is `var zero ≐ var (suc (suc (suc (suc (suc (suc w))))))`
  -- (src/L/Condensation.lagda.md:7010), and at KValue's frame `w` is
  -- the carrier index `iA`, because `KFacts`'s first parameter is the
  -- carrier (src/L/Condensation.lagda.md:6680-6682) and `[LJ-1.495]`
  -- instantiated it at `iA` (agents/tasks/LJ-1-495/Probe495.agda:169).
  -- So the pin says slot 0 IS slot 6.  This vector satisfies it
  -- DEFINITIONALLY, and that is a stronger reason for slot 0 than the
  -- `envK-*` census: the carrier occupies slot 0 AND slot 6, by design.
  pin-holds : lookup zero gammaPrime ≡ lookup (suc (suc (suc (suc (suc (suc KV.iA)))))) gammaPrime
  pin-holds = refl

  -- Slot 7, at the index EVERY K-field reaches: `suc^6 K` with K := iK.
  slotK-is-bound : lookup (suc (suc (suc (suc (suc (suc KV.iK)))))) gammaPrime
                 ≡ LsetS lam ordλ
  slotK-is-bound = refl

  -- Slots 8..19, at the indices `tagEq0` .. `tagEq11` reach.
  tag0 : lookup (suc (suc (suc (suc (suc (suc KV.i0)))))) gammaPrime ≡ numeralL 0
  tag0 = refl
  tag1 : lookup (suc (suc (suc (suc (suc (suc KV.i1)))))) gammaPrime ≡ numeralL 1
  tag1 = refl
  tag2 : lookup (suc (suc (suc (suc (suc (suc KV.i2)))))) gammaPrime ≡ numeralL 2
  tag2 = refl
  tag3 : lookup (suc (suc (suc (suc (suc (suc KV.i3)))))) gammaPrime ≡ numeralL 3
  tag3 = refl
  tag4 : lookup (suc (suc (suc (suc (suc (suc KV.i4)))))) gammaPrime ≡ numeralL 4
  tag4 = refl
  tag5 : lookup (suc (suc (suc (suc (suc (suc KV.i5)))))) gammaPrime ≡ numeralL 5
  tag5 = refl
  tag6 : lookup (suc (suc (suc (suc (suc (suc KV.i6)))))) gammaPrime ≡ numeralL 6
  tag6 = refl
  tag7 : lookup (suc (suc (suc (suc (suc (suc KV.i7)))))) gammaPrime ≡ numeralL 7
  tag7 = refl
  tag8 : lookup (suc (suc (suc (suc (suc (suc KV.i8)))))) gammaPrime ≡ numeralL 8
  tag8 = refl
  tag9 : lookup (suc (suc (suc (suc (suc (suc KV.i9)))))) gammaPrime ≡ numeralL 9
  tag9 = refl
  tag10 : lookup (suc (suc (suc (suc (suc (suc KV.i10)))))) gammaPrime ≡ numeralL 10
  tag10 = refl
  tag11 : lookup (suc (suc (suc (suc (suc (suc KV.i11)))))) gammaPrime ≡ numeralL 11
  tag11 = refl

  -- `[LJ-1.502]` is GO and its identification is `t0 := N0`, `t1 := N1`.
  -- At this vector `t0eq` and `t1eq` then ask of slots 8 and 9 exactly
  -- what `tagEq0` and `tagEq1` ask, so ONE `refl` stands in both field
  -- positions.  Taken, not re-opened.
  t0-serves-both : lookup (suc (suc (suc (suc (suc (suc KV.i0)))))) gammaPrime ≡ numeralL 0
  t0-serves-both = tag0
  t1-serves-both : lookup (suc (suc (suc (suc (suc (suc KV.i1)))))) gammaPrime ≡ numeralL 1
  t1-serves-both = tag1

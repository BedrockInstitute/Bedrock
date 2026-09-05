{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.646] PROBE.  Naming Lset in the hull's language, at an ordinal code.
-- It runs in agents/tasks/LJ-1-646/ and lands nothing in src/.
--
--   FRAME FIRST      the telescope, the predecessor's terms imported
--                    (not copied: agents/README.md:76).  Floor 2.90 s
--                    (runs/floor-0.time).
--
--   SHAPE A WALLED   the read-off written inline at the concrete
--                    packaged graph.  1.6 GB resident and still running
--                    at 5 min under the 2 GB cap.  Killed, kept at
--                    runs/SHAPE-A-inline.agda.txt.  Cause: the concrete
--                    formula normalizes inside the satisfaction (P-l).
--
--   SHAPE B          every row generic in the formula.  The graph is an
--                    ATOM to the elaborator and nothing unfolds.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M2g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-646.Probe646 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import FOL.Manipulation.Parameters using ( countFo )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; Lset )
open import L.Hull {ℓ} lem using ( module AtStage )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset→∈ )
open import L.WellOrder.Base {ℓ-suc ℓ} using ( leastOf )
open import L.Coding.Sequence {ℓ} lem using ( LsetGraph )

open import Cubical.Data.Nat using ( ℕ )
open import Cubical.Data.Sigma using ( Σ-syntax )
open import Cubical.Data.Vec using ( Vec; _∷_ )
open import Cubical.HITs.PropositionalTruncation using ( ∣_∣₁ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; module InfinitySet )
open InfinitySet using ( sucV )

import LJ-1-474.Probe474 as Pred474
module Q = Pred474 {ℓ} lem

import LJ-1-642.Probe642 as Pred642
module R = Pred642 {ℓ} lem

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- The graph's constant budget.  One name, so no row recomputes it.
N : ℕ
N = countFo LsetGraph

-- Telescope copied from src/L/BoundedSubset.lagda.md:903-905, the same
-- six parameters the predecessor carries (Probe474.agda:88-91).

module HullStage (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : S) (X⊆L : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  module ASt = AtStage lam ordλ

  module H = ASt.Hull X X⊆L ∅∈λ

  -- The predecessors' own instances.  feed and lset-codes are taken from
  -- [LJ-1.474] (Probe474.agda:124-131); the level's membership in the
  -- stage is taken from [LJ-1.642] (Probe642.agda:327-337).  Neither is
  -- rebuilt here: a copy would be a second measurement of one object.
  module P = Q.HullStage lam ordλ succλ X X⊆L ∅∈λ
  module F = R.Frame lam ordλ succλ X X⊆L ∅∈λ

  open H.T using ( Code; val; vals; Sat; val-wit; wit; _⊨₀_ )

  -- =====================================================================
  -- THE OBLIGATION, stated.
  -- =====================================================================

  LsetCodeOrd : Type (ℓ-suc ℓ)
  LsetCodeOrd =
    (c : Code) → IsOrd (fst (val c))
    → Σ[ d ∈ Code ] (fst (val d) ≡ Lset (fst (val c)))

  -- =====================================================================
  -- STEP ONE.  The ordinality join [LJ-1.479] could not find.
  -- [LJ-1.479] asked for IsOrd FROM hull membership and stopped
  -- (lj-1.479-report.md:84-88).  This brief GIVES IsOrd, and the
  -- converse is then one line: ord∈Lset→∈ at
  -- src/L/Ordinal/Stages.lagda.md:265-268.
  -- =====================================================================

  code-ord-mem : (c : Code) → IsOrd (fst (val c)) → ⟨ fst (val c) ∈ˢ lam ⟩
  code-ord-mem c oc = ord∈Lset→∈ lam ordλ (fst (val c)) oc (snd (val c))

  -- THE TARGET VALUE LIVES IN THE STAGE CARRIER, AND [LJ-1.642] ALREADY
  -- PROVED IT.  level-in-stage is Probe642.agda:330-337 and
  -- level-of-code-in-stage is :339-341.  It is taken, not rebuilt.  So
  -- DEVLIN 2.6(ii) IS MISSING ONLY ITS WITNESS z, NOT ITS VALUE
  -- (dev/literature/devlin-II5.md:220-222).
  Lset-code-in-stage : (c : Code) → IsOrd (fst (val c))
                     → ⟨ Lset (fst (val c)) ∈ˢ Lset lam ⟩
  Lset-code-in-stage = F.level-of-code-in-stage

  -- The stage element a code for the tower must name.
  LsetAt : (c : Code) → IsOrd (fst (val c)) → ASt.SL
  LsetAt c oc = Lset (fst (val c)) , Lset-code-in-stage c oc

  -- =====================================================================
  -- STEP TWO.  What a wit code's value is.  GENERIC IN THE FORMULA:
  -- the graph never enters a type here, so nothing normalizes (P-l).
  -- =====================================================================

  module Wit (k : ℕ) (ψ : Formula (⊥* {ℓ}) (suc k)) (cs : Vec Code k) where

    -- The value of a wit code satisfies the code's own formula, as soon
    -- as the STAGE has any witness at all.  This is the only thing wit
    -- gives, and it is the whole of it.
    wit-sat : (w : Sat k ψ (vals cs)) → ⟨ (val (wit k ψ cs) ∷ vals cs) ⊨₀ ψ ⟩
    wit-sat w =
      subst (λ a → ⟨ (a ∷ vals cs) ⊨₀ ψ ⟩) (sym (val-wit k ψ cs w))
        (leastOf ASt.wL {ℓ'' = ℓ-suc ℓ} lem
          (λ a → (a ∷ vals cs) ⊨₀ ψ) w .snd .fst)

  -- =====================================================================
  -- STEP THREE.  The obligation reduced to two named residues, and the
  -- reduction TYPECHECKED.  GENERIC IN THE FORMULA for the same reason
  -- step two is: the graph must not enter a type (P-l).  The
  -- predecessor's own choice is named below, by module application.
  -- =====================================================================

  module Reduce (k : ℕ) (ψ : Formula (⊥* {ℓ}) (suc k))
                (cs : Code → Vec Code k) where

    -- RESIDUE ONE.  The STAGE believes ψ at the code.  Without it
    -- val (wit k ψ (cs c)) is the junk value and not a witness at all
    -- (src/L/Hull.lagda.md:90-91).
    StageSat : Type (ℓ-suc ℓ)
    StageSat = (c : Code) → IsOrd (fst (val c)) → Sat k ψ (vals (cs c))

    -- RESIDUE TWO.  A stage witness of ψ IS the tower there.  This is
    -- Lset-only's conclusion (src/L/Hierarchy.lagda.md:334-335) asked at
    -- the STAGE carrier instead of the constructible-class carrier.
    ReadOff : Type (ℓ-suc ℓ)
    ReadOff = (c : Code) (a : ASt.SL) → IsOrd (fst (val c))
            → ⟨ (a ∷ vals (cs c)) ⊨₀ ψ ⟩
            → fst a ≡ Lset (fst (val c))

    -- RESIDUE ONE, IN DEVLIN'S OWN SHAPE.  The stage sees ψ hold OF THE
    -- TOWER at the code.  This is requirement 2, and the value slot is
    -- no longer part of the debt: LsetAt supplies it.
    StageHolds : Type (ℓ-suc ℓ)
    StageHolds = (c : Code) (oc : IsOrd (fst (val c)))
               → ⟨ (LsetAt c oc ∷ vals (cs c)) ⊨₀ ψ ⟩

    holds→sat : StageHolds → StageSat
    holds→sat h c oc = ∣ LsetAt c oc , h c oc ∣₁

    -- The obligation is exactly those two, and nothing else.
    join : StageSat → ReadOff → LsetCodeOrd
    join sat read c oc =
        wit k ψ (cs c)
      , read c (val (wit k ψ (cs c))) oc
          (Wit.wit-sat k ψ (cs c) (sat c oc))

  -- The predecessor's instance, named.  feed is wit at the packaged
  -- graph with [LJ-1.474]'s constant codes (Probe474.agda:125, :131).
  module Feed646 = Reduce (suc N) Q.packaged (λ c → c ∷ P.lset-codes)

  -- AND THE IDENTIFICATION IS MACHINE-CHECKED, NOT READ.  The code the
  -- reduction returns at that instance IS the predecessor's feed.  Three
  -- separate module applications of AtStage.Hull at these six
  -- parameters, [LJ-1.474]'s, [LJ-1.642]'s (through src HullStage) and
  -- this file's, are therefore one alphabet.
  feed≡ : (c : Code) → P.feed c ≡ wit (suc N) Q.packaged (c ∷ P.lset-codes)
  feed≡ c = refl

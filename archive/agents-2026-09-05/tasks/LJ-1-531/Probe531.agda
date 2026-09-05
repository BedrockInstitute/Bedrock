{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.531]  THE REPLACEMENT RANK IS INJECTIVE ON THE MEMBERS OF `a`.
--
-- The obligation is `rank-at′-inj`, section 4.  Section 1 is W3, the
-- extensionality of the order, written first and typechecked ALONE
-- (agents/tasks/LJ-1-531/runs/W3.agda, runs/w3-1.out to w3-3.out).
--
-- D-10 FIRST, AND THE ANSWER IS THAT THE LEMMA IS TRUE.  The brief asks
-- whether the order `swo-rank′` recurses on is extensional, and orders a
-- refutation if it is not.  It is, and NOT because the ordinal site is
-- extensional: `P521.swo-rank′` recurses on `SWO._<∙_ w` and on nothing
-- else (Probe521.agda:234-244, where `Rank′.Pred a` is
-- `Σ[ x ∈ A ] (x <∙ a)` and `step`/`go` read no other datum), and the
-- `SWO` record CARRIES trichotomy and irreflexivity as fields `tri∙` and
-- `irr∙` (src/L/WellOrder/Base.lagda.md:104-105).  Two record fields, at
-- the generic carrier, are the whole of the extensionality.  Section 1
-- proves it and section 2 spends it.
--
-- ONE IMPORT OF A PREDECESSOR PROBE, and it is the SAME necessity
-- [LJ-1.529] measured and declared (agents/tasks/LJ-1-529/Probe529.agda:16-30,
-- lj-1.529-report.md "ONE DEPARTURE FROM PREDECESSOR PRACTICE, DECLARED").
-- `bedrock.agda-lib:2` lists `agents/tasks` as an include root, and the
-- tree already carries cross-task probe imports
-- (agents/tasks/LJ-1-184/ProbeLJ1184C.agda:29,
-- agents/tasks/LJ-1-224/ProbeGraphSupply.agda:24).
--
-- HERE THE NECESSITY IS SHARPER THAN [LJ-1.529]'s AND THAT IS THIS
-- TASK'S OWN FINDING.  `P521.swo-rank′` is SEALED
-- (Probe521.agda:380-402, `opaque`), and the seal exports exactly five
-- names.  The obligation's proof needs `rank-mem-in`, one of the five.
-- A rebuilt `swo-rank′` would be a different opaque term, `rank-at′-val`
-- (Probe521.agda:438-442) would not connect it to `rank-at′`, and there
-- is no route from outside the seal to the recursion.  So on a no-import
-- route this task is a rebuild of Probe521, priced at 1176 lines
-- (agents/tasks/LJ-1-521/lj-1.521-report.md:287).
--
-- `[LJ-1.515]`'s `swo-rank′-mem` (Probe515.agda:224-226) is the
-- monotonicity this argument wants, AND IT IS NOT REACHABLE.  It is
-- stated about [LJ-1.515]'s OWN `swo-rank′`, which is a different term
-- from the sealed one; [LJ-1.521] did not rebuild it
-- (lj-1.521-report.md:350-352).  Section 2 derives it instead, from
-- `rank-mem-in` and `self∈sucV`, and the derivation crosses the
-- `_∈ᵗ_`/`_∈ₛ_` boundary exactly once, which [LJ-1.529] predicted as
-- reasoning and this file measures.
--
-- `Bound′` AND `rank-bound′` ARE NOT REBUILT.  [LJ-1.529] delivered them
-- at 33 code lines (Probe529.agda:101-142) and the brief says take them.
-- The obligation does not mention the bound, so this file does not carry
-- them at all; section 5 of the report says where they are.
--
-- `injAt` IS NOT BUILT.  `domAt` IS NOT TOUCHED.  Nothing lands in src/.
-- Does not postulate.  `swo-rank`, the rank [LJ-1.497] refuted, appears
-- nowhere in this file but in this sentence.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-531.Probe531 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import V.Presentation {ℓ} using ( fiber )
open import V.Model {ℓ} using ( self∈sucV )
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd )
open import L.WellOrder.Base {ℓ} using ( SWO; Tri; lt; eq; gt )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; _∈ₛ_; ∈∈ₛ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( sucV )
import Cubical.Data.Empty as Empty

import LJ-1-521.Probe521 {ℓ} lem as P521

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )

-- =====================================================================
-- 1.  W3, THE EXTENSIONALITY OF THE ORDER.  This is
--     agents/tasks/LJ-1-531/runs/W3.agda, repeated here because a file
--     cannot import the slice it was cut from.
--
--     TWO TERMS, AND THE SECOND IS THE ONE THE OBLIGATION SPENDS.
--     `preds-distinguish` is the brief's named shape, and it is what
--     answers D-10: agreeing predecessor sets force equality.
--     `mono→inj` is the same two record fields used directly, and it
--     says the general fact: over a strict total well-order, ANY
--     strictly monotone map into ANY irreflexive relation is injective.
--     Section 3 instantiates it once.
--
--     THE ONE CHANGE FROM runs/W3.agda: `mono→inj`'s codomain is
--     generalised in its two levels, because section 3 instantiates
--     `B := V ℓ`, which lives in `Type (ℓ-suc ℓ)` and not in `Type ℓ`.
--     W3 measured the shape at `Type ℓ` and it is the same proof.
-- =====================================================================

module _ {A : Type ℓ} (w : SWO {ℓc = ℓ} A) where
  open SWO w

  preds-distinguish :
      (j k : A)
    → ((x : A) → x <∙ j → x <∙ k)
    → ((x : A) → x <∙ k → x <∙ j)
    → j ≡ k
  preds-distinguish j k to fro = go (tri∙ j k)
    where
    go : Tri (j <∙ k) (j ≡ k) (k <∙ j) → j ≡ k
    go (lt h) = Empty.rec (irr∙ j (fro j h))
    go (eq p) = p
    go (gt h) = Empty.rec (irr∙ k (to k h))

  mono→inj :
      {ℓb ℓr : Level} {B : Type ℓb} (R : B → B → Type ℓr)
    → ((b : B) → R b b → Empty.⊥)
    → (f : A → B)
    → ((x y : A) → x <∙ y → R (f x) (f y))
    → (j k : A) → f j ≡ f k → j ≡ k
  mono→inj R irrR f mono j k p = go (tri∙ j k)
    where
    go : Tri (j <∙ k) (j ≡ k) (k <∙ j) → j ≡ k
    go (lt h) =
      Empty.rec (irrR (f k) (subst (λ v → R v (f k)) p (mono j k h)))
    go (eq q) = q
    go (gt h) =
      Empty.rec (irrR (f j) (subst (λ v → R v (f j)) (sym p) (mono k j h)))

-- =====================================================================
-- 2.  MONOTONICITY OF THE SEALED RANK, AND THE ONE RELATION CROSSING.
--
--     [LJ-1.515] states this about its own rank (Probe515.agda:224-226)
--     and that statement does not reach the sealed rank; see the file
--     head.  Here it is derived from `P521.rank-mem-in`
--     (Probe521.agda:399-402) at `u := swo-rank′ w j`, with `self∈sucV`
--     (src/V/Model.lagda.md:236-237) supplying the successor membership.
--
--     THE CROSSING IS ONE `∈∈ₛ` AND IT IS IN `rank-mono` ALONE.
--     `self∈sucV` speaks `_∈ˢ_` at `𝒮ᵥ`; `rank-mem-in` wants `_∈ₛ_`,
--     the library's small membership.  `∈∈ₛ .fst` converts, and
--     `∈ₛ-irrefl` below converts back once so that `∈-irrefl`
--     (src/V/Hierarchy.lagda.md:155-156) can be the irreflexivity
--     `mono→inj` asks for.  Two uses, no transport, no adapter module.
-- =====================================================================

∈ₛ-irrefl : (u : V ℓ) → ⟨ u ∈ₛ u ⟩ → Empty.⊥
∈ₛ-irrefl u h = ∈-irrefl u (∈∈ₛ {a = u} {b = u} .snd h)

rank-mono :
    {A : Type ℓ} (w : SWO {ℓc = ℓ} A) (j k : A)
  → SWO._<∙_ w j k
  → ⟨ P521.swo-rank′ w j ∈ₛ P521.swo-rank′ w k ⟩
rank-mono w j k h =
  P521.rank-mem-in w k r j h (∈∈ₛ {a = r} {b = sucV r} .fst (self∈sucV r))
  where
  r : V ℓ
  r = P521.swo-rank′ w j

-- =====================================================================
-- 3.  THE RANK IS INJECTIVE, AT THE GENERIC CARRIER.  This is clause W2:
--     the mathematics is written once at `SWO`, and section 4
--     instantiates it at the one order the counting leg has.
-- =====================================================================

swo-rank′-inj :
    {A : Type ℓ} (w : SWO {ℓc = ℓ} A) (j k : A)
  → P521.swo-rank′ w j ≡ P521.swo-rank′ w k → j ≡ k
swo-rank′-inj w =
  mono→inj w (λ u v → ⟨ u ∈ₛ v ⟩) ∈ₛ-irrefl (P521.swo-rank′ w) (rank-mono w)

-- =====================================================================
-- 4.  THE OBLIGATION.  `rank-at′` (Probe521.agda:428-436) is the rank at
--     a MEMBER of `a`, and its one exported equation `rank-at′-val`
--     (:438-442) says the value is `swo-rank′` at that member's fibre
--     index.  So section 3 gives equality of the two indices, and
--     `fiber`'s second component (src/V/Presentation.lagda.md:34-35)
--     carries it back to the members themselves.
--
--     THE TELESCOPE IS THE BRIEF'S, VERBATIM.  No `Q`, no `bnd`, no
--     `ord-reads-Q`: the statement does not mention the carve, and
--     nothing here reads the bound.
-- =====================================================================

rank-at′-inj :
    (a : S) (oa : IsOrd (fst a)) (m m' : S)
    (mx : ⟨ fst m ∈ fst a ⟩) (mx' : ⟨ fst m' ∈ fst a ⟩)
  → fst (P521.rank-at′ a oa m mx) ≡ fst (P521.rank-at′ a oa m' mx')
  → fst m ≡ fst m'
rank-at′-inj a oa m m' mx mx' p =
  sym (fiber (fst a) mx .snd) ∙ cong ⟪ fst a ⟫↪ kp ∙ fiber (fst a) mx' .snd
  where
  w : SWO {ℓc = ℓ} ⟪ fst a ⟫
  w = P521.OrdSWO∈ₛ.w (fst a) oa

  ranks : P521.swo-rank′ w (fiber (fst a) mx .fst)
        ≡ P521.swo-rank′ w (fiber (fst a) mx' .fst)
  ranks = sym (P521.rank-at′-val a oa m mx)
        ∙ p
        ∙ P521.rank-at′-val a oa m' mx'

  kp : fiber (fst a) mx .fst ≡ fiber (fst a) mx' .fst
  kp = swo-rank′-inj w (fiber (fst a) mx .fst) (fiber (fst a) mx' .fst) ranks

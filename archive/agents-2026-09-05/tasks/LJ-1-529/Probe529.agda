{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.529]  THE RANGE CLAUSE, over the carve re-based on `swo-rank′`.
--
-- The obligation is `range-clause`, section 6.  Section 1 is W3, the
-- re-basing, written first and typechecked ALONE
-- (agents/tasks/LJ-1-529/runs/W3.agda, runs/w3-1.out to w3-3.out).
--
-- WHICH CONJUNCT THIS IS.  The brief calls it "the second of the four
-- `InjCode` conjuncts".  It is the second DELIVERED, after [LJ-1.524]'s
-- `svAt`; POSITIONALLY it is the fourth of `InjCode`'s four components
-- (src/L/Cardinal.lagda.md:223-228), which is what [LJ-1.490] and
-- [LJ-1.521] both call it.  Section 5 reads the type out of `InjCode`
-- itself so that neither reading can drift.
--
-- ONE IMPORT OF A PREDECESSOR PROBE, and it is deliberate.  [LJ-1.524]
-- declared the same import and gave the whole argument in its report
-- ("ONE DEPARTURE FROM THE PREDECESSORS' PRACTICE, DECLARED"):
-- `bedrock.agda-lib:2` lists `agents/tasks` as an include root, the tree
-- already carries cross-task probe imports
-- (agents/tasks/LJ-1-184/ProbeLJ1184C.agda:29,
-- agents/tasks/LJ-1-224/ProbeGraphSupply.agda:24), and no rule in
-- `AGENTS.md`, `dev/pod/instructions/coder.md`, `dev/LESSONS.md`,
-- `dev/pod/rulings.toml` or `agents/README.md` forbids it.
--
-- HERE THE IMPORT IS MORE THAN AN ECONOMY, and section 1 says why: the
-- re-basing must be formed at the SAME `SWO` record `P521.rank-at′` runs
-- on, or the rank the clause reads and the ordinal the pack bounds are
-- two different terms and nothing connects them.  A rebuilt copy of
-- `OrdSWO∈ₛ` would be a different record.
--
-- REBUILT HERE, and nothing else is:
--   * section 2, [LJ-1.490]'s `rank-graph` and `rank-graph-out`
--     (Probe490.agda:105-116), at [LJ-1.521]'s `rankFo`.  Four lines.
--     [LJ-1.490] is NOT imported: its `Bound`, `C` and `bnd` are built on
--     `swo-rank`, the rank [LJ-1.497] refuted, and importing the module
--     would pull the refuted rank into this file.
--   * section 3, [LJ-1.524]'s instantiation of `Q` (Probe524.agda:106-115).
--
-- `swo-rank` INHABITS NO TERM OF THIS FILE.  It is named only in the
-- comments that say what is NOT restored.  Nothing lands in src/.  Does
-- not postulate.  `rankFo-adequate′` is NOT rebuilt.  `injAt` and `domAt`
-- are NOT attempted.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-529.Probe529 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; pr-inj )
open import V.Presentation {ℓ} using ( fiber )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; IsOrd )
open import L.Ordinal {ℓ} using ( boundingOrd )
open import L.InjChain {ℓ} lem using ( module PairBound )
open import L.WellOrder.Base {ℓ} using ( SWO )
open import L.Axioms.Full {ℓ} lem using ( hasSeparationL )
open import L.Cardinal {ℓ} lem using ( InjCode )
open import L.Coding.Model {ℓ} using ( prʟ; prʟ-fst )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )

import LJ-1-521.Probe521 {ℓ} lem as P521

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- =====================================================================
-- 1.  W3, THE RE-BASING.  [LJ-1.490]'s `Bound` (Probe490.agda:211-230)
--     and `rank-bound` (:233-242) with `P521.swo-rank′` where they have
--     `swo-rank`.  This is runs/W3.agda, repeated here because a file
--     cannot import the slice it was cut from.
--
--     TWO SUBSTITUTIONS AND NOT ONE, and the second is forced.
--     [LJ-1.490] imports `L.WellOrder.Base {ℓ-suc ℓ}` (Probe490.agda:34)
--     and builds its own `OrdSWO` on `_∈ᵗ_` (Probe490.agda:165-201);
--     [LJ-1.521] imports the same module at `{ℓ}` (Probe521.agda:53) and
--     builds `OrdSWO∈ₛ` on `_∈ₛ_` (Probe521.agda:174-216).
--     `P521.swo-rank′` accepts only the second.  More than that:
--     `P521.rank-at′` (Probe521.agda:428-436) runs on
--     `P521.OrdSWO∈ₛ.w (fst a) oa` and on no other record, and section 6
--     must put the value of `rank-at′` inside the ordinal this pack
--     bounds.  So the order is substituted too, and it is a substitution
--     of a DELIVERED term for a DELIVERED term, not a new proof.
--
--     THREE LINES BELOW ARE MINE AND NOT [LJ-1.490]'s: the signatures of
--     `w`, `β` and `oβ`, which [LJ-1.490] leaves to inference.  Dropping
--     them makes this block 20 code lines, exactly [LJ-1.490]'s count,
--     and it still typechecks (agents/tasks/LJ-1-529/runs/W3-noasc.agda,
--     runs/w3-noasc.out, exit 0).  They are kept because `w` is the one
--     place a reader must see WHICH `SWO` record the pack is formed at.
-- =====================================================================

module Bound′ (a : S) (oa : IsOrd (fst a)) where

  w : SWO {ℓc = ℓ} ⟪ fst a ⟫
  w = P521.OrdSWO∈ₛ.w (fst a) oa

  pack = boundingOrd ⟪ fst a ⟫ (P521.swo-rank′ w) (P521.swo-rank′-ord w)

  β : V ℓ
  β = pack .fst

  oβ : IsOrd β
  oβ = pack .snd .fst

  C : S
  C = β , P521.isL-ord β oβ

  module PB = PairBound a C

  bnd : S
  bnd = PB.bnd

  below : (m : S) (mx : ⟨ fst m ∈ fst a ⟩)
        → ⟨ pr (fst m) (P521.swo-rank′ w (fiber (fst a) mx .fst)) ∈ fst bnd ⟩
  below m mx = PB.below m z mx r∈β
    where
    k = fiber (fst a) mx .fst
    r = P521.swo-rank′ w k
    r∈β : ⟨ r ∈ β ⟩
    r∈β = pack .snd .snd k
    z : S
    z = r , isL-trans {x = β} {y = r} r∈β (snd C)

rank-bound′ :
    (a : S) (oa : IsOrd (fst a))
  → Σ[ bnd ∈ S ]
      ((m : S) (mx : ⟨ fst m ∈ fst a ⟩)
        → ⟨ pr (fst m) (P521.swo-rank′ (P521.OrdSWO∈ₛ.w (fst a) oa)
                                       (fiber (fst a) mx .fst))
            ∈ fst bnd ⟩)
rank-bound′ a oa = Rb.bnd , Rb.below
  where
  module Rb = Bound′ a oa

-- =====================================================================
-- 2.  THE CARVE.  [LJ-1.490]'s (Probe490.agda:105-116), at [LJ-1.521]'s
--     `rankFo`.  `bnd` stays a parameter here; section 5 feeds it the
--     RE-BASED bound and nothing else.
-- =====================================================================

rank-graph :
    (Q a bnd : S)
  → Σ[ G ∈ S ] ((z : S) → (z ∈ˢ G)
      ≡ ((z ∈ˢ bnd) ⊓ ((z ∷ []) ⊨ P521.rankFo Q a)))
rank-graph Q a bnd = hasSeparationL bnd (P521.rankFo Q a) .fst

rank-graph-out :
    (Q a bnd z : S)
  → ⟨ z ∈ˢ fst (rank-graph Q a bnd) ⟩
  → ⟨ z ∈ˢ bnd ⟩ × ⟨ (z ∷ []) ⊨ P521.rankFo Q a ⟩
rank-graph-out Q a bnd z h =
  subst ⟨_⟩ (snd (rank-graph Q a bnd) z) h

-- =====================================================================
-- 3.  `Q` IS INSTANTIATED AND NOT HYPOTHESISED.  [LJ-1.524]'s
--     (Probe524.agda:106-115), which is the mathematician's standing
--     ruling confirmed against a real consumer.
-- =====================================================================

ordQ : (a : S) → IsOrd (fst a) → S
ordQ a oa = P521.ord-set-witness a oa .fst

adequate-at-witness :
    (a : S) (oa : IsOrd (fst a)) (z : S)
  → ⟨ (z ∷ []) ⊨ P521.rankFo (ordQ a oa) a ⟩
  → Σ[ m ∈ S ] Σ[ mx ∈ ⟨ fst m ∈ fst a ⟩ ]
      (fst z ≡ pr (fst m) (fst (P521.rank-at′ a oa m mx)))
adequate-at-witness a oa z =
  P521.rankFo-adequate′ (ordQ a oa) a oa z (P521.ord-set-witness a oa .snd)

-- =====================================================================
-- 4.  THE CONJUNCT'S TYPE, read out of `InjCode` so that nothing can
--     drift (src/L/Cardinal.lagda.md:223-228).  `RangeOf F b` is the
--     FOURTH component there, and the projection below typechecks only if
--     it is definitionally that component.
-- =====================================================================

RangeOf : S → S → Type (ℓ-suc ℓ)
RangeOf F b = (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst F ⟩ → ⟨ fst y ∈ fst b ⟩

range-is-fourth-of-InjCode : (F a b : S) → InjCode F a b → RangeOf F b
range-is-fourth-of-InjCode F a b h = h .snd .snd .snd

-- =====================================================================
-- 5.  THE CARVE OVER THE RE-BASED BOUND, AND THE OBLIGATION OVER IT.
--
--     ONE NAME FOR THE CARVE, ONE NAME FOR THE CODOMAIN, AND NOWHERE
--     THEIR BODIES.  This is [LJ-1.524]'s measured design law
--     (agents/tasks/LJ-1-524/lj-1.524-report.md, section 3) and it is
--     carried here rather than re-derived: `G` and `C` below each appear
--     as a name in every type that mentions them, and each body is
--     written once.
--
--     `bnd` IS NOT FREE HERE AND THAT IS THE TASK.  [LJ-1.524] proved
--     `svAt` at a free `bnd` and reported that `svAt` never reads the
--     bound.  The range clause is different: its codomain `b` is `C`,
--     the bounding ordinal the pack forms, and `C` and `bnd` come out of
--     ONE `boundingOrd` on the rank.  So this conjunct is the one that
--     spends the re-basing.
-- =====================================================================

module Carve (a : S) (oa : IsOrd (fst a)) where

  module B = Bound′ a oa

  Q : S
  Q = ordQ a oa

  C : S
  C = B.C

  G : S
  G = fst (rank-graph Q a B.bnd)

  -- 5.1  the reading.  [LJ-1.524]'s `sat`/`read`/`val`
  --      (Probe524.agda:206-228), at the re-based bound.  `prʟ-fst`
  --      (src/L/Coding/Model.lagda.md:329-330) enters, `rank-graph-out`
  --      leaves with satisfaction, `adequate-at-witness` reads, `pr-inj`
  --      (src/V/Coding.lagda.md:178-179) splits.  No adapter.

  Hold : S → S → Type (ℓ-suc ℓ)
  Hold x y = ⟨ pr (fst x) (fst y) ∈ fst G ⟩

  sat : (x y : S) → Hold x y → ⟨ (prʟ x y ∷ []) ⊨ P521.rankFo Q a ⟩
  sat x y h = rank-graph-out Q a B.bnd (prʟ x y) inG .snd
    where
    inG : ⟨ prʟ x y ∈ˢ G ⟩
    inG = subst (λ v → ⟨ v ∈ fst G ⟩) (sym (prʟ-fst x y)) h

  read : (x y : S) → Hold x y
       → Σ[ m ∈ S ] Σ[ mx ∈ ⟨ fst m ∈ fst a ⟩ ]
           (pr (fst x) (fst y) ≡ pr (fst m) (fst (P521.rank-at′ a oa m mx)))
  read x y h =
    t .fst , (t .snd .fst , sym (prʟ-fst x y) ∙ t .snd .snd)
    where
    t = adequate-at-witness a oa (prʟ x y) (sat x y h)

  -- the value is the rank at that member
  val : (x y : S) (h : Hold x y)
      → fst y ≡ fst (P521.rank-at′ a oa (read x y h .fst)
                                        (read x y h .snd .fst))
  val x y h = pr-inj (read x y h .snd .snd) .snd

  -- 5.2  THE ONE STEP THE RE-BASING BUYS.  `rank-at′-val`
  --      (Probe521.agda:438-442) is the equation the seal exports, and
  --      `pack`'s third component (src/L/Ordinal.lagda.md:155) is the
  --      membership.  Both are at `B.w`, and `B.w` is the record
  --      `rank-at′` itself runs on, so the two terms meet without a
  --      transport of the order.

  rank-in-C : (m : S) (mx : ⟨ fst m ∈ fst a ⟩)
            → ⟨ fst (P521.rank-at′ a oa m mx) ∈ fst C ⟩
  rank-in-C m mx =
    subst (λ v → ⟨ v ∈ fst C ⟩)
      (sym (P521.rank-at′-val a oa m mx))
      (B.pack .snd .snd (fiber (fst a) mx .fst))

  -- 5.3  the clause: the second component of a pair in the carve is the
  --      rank at a member, and every rank is below the bounding ordinal.

  ran : RangeOf G C
  ran x y h =
    subst (λ v → ⟨ v ∈ fst C ⟩) (sym (val x y h))
      (rank-in-C (read x y h .fst) (read x y h .snd .fst))

-- =====================================================================
-- 6.  THE OBLIGATION.  `Carve.G a oa` is the carve over the RE-BASED
--     bound and `Carve.C a oa` is the re-based bounding ordinal; section
--     5 defines each in one line, and the type says the name and not the
--     body for the reason [LJ-1.524] measured.
-- =====================================================================

range-clause :
    (a : S) (oa : IsOrd (fst a))
  → RangeOf (Carve.G a oa) (Carve.C a oa)
range-clause = Carve.ran

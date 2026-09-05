{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.559]  `domAt`, the SECOND of `InjCode`'s four conjuncts by
-- position (src/L/Cardinal.lagda.md:226) and the LAST of the four to be
-- delivered, over the rank carve, with `Q` DETERMINED.
--
-- The obligation is `domAt-at-carve`, section 7.  Section 0 is W3, the
-- FLOOR: this file's import set with the obligation's type and no proof,
-- typechecked ALONE (agents/tasks/LJ-1-559/runs/W3.agda, runs/w3-1.out
-- to w3-3.out).
--
-- WHY `domAt` IS NOT ITS THREE SIBLINGS.  `svAt` ([LJ-1.524]), `injAt`
-- ([LJ-1.531]) and the value-in-b clause ([LJ-1.529]) all READ the carve:
-- each takes a pair already in it and says something about that pair.
-- `domAt` is stated as two implications (src/L/Coding/Model.lagda.md:278-280)
-- and the second one WRITES: given `x ∈ a`, it must EXHIBIT a pair of the
-- carve at `x`.  So this conjunct, alone of the four, needs
--   (a) the converse of `rankFo-adequate′`, which [LJ-1.521] did not
--       build and which section 5 assembles from [LJ-1.537], and
--   (b) a bound that actually COVERS the rank pairs, where [LJ-1.524]
--       could leave `bnd` a free parameter because `svAt` never reads it
--       (Probe524.agda:181-186).
-- That is the whole of the difference, and it is why two dispatches ran
-- out of time on it.
--
-- IMPORTS OF PREDECESSOR PROBES, and both are declared.
--   * `P521`, for `rankFo`, `rank-at′`, `swo-rank′` and
--     `rankFo-adequate′`.  [LJ-1.524] gave the whole argument for a
--     cross-task probe import in its report and [LJ-1.529] repeated it:
--     `bedrock.agda-lib:2` lists `agents/tasks` as an include root, the
--     tree already carries such imports
--     (agents/tasks/LJ-1-184/ProbeLJ1184C.agda:29,
--     agents/tasks/LJ-1-224/ProbeGraphSupply.agda:24), and no rule in
--     `AGENTS.md`, `dev/pod/instructions/coder.md`, `dev/LESSONS.md`,
--     `dev/pod/rulings.toml` or `agents/README.md` forbids it.
--   * `P537`, for `approx-carve`.  Premise 8 of the brief names
--     [LJ-1.537] as having built it and pinned its type; its report
--     carries `verdict: GO` (agents/tasks/LJ-1-537/lj-1.537-report.md:6)
--     and the type is the one that typechecked
--     (agents/tasks/LJ-1-537/Probe537.agda:616-620).  Section 5 uses
--     that type and no other.
--
-- THE THREE CONJUNCT PROBES ARE NOT IMPORTED.  The brief forbids it and
-- nothing here needs them: `[LJ-1.529]`'s section 1 is REBUILT below as
-- section 1, exactly as [LJ-1.529] itself rebuilt it from [LJ-1.490].
--
-- `InjCode` IS NOT ASSEMBLED.  B9 is not touched.  Nothing lands in
-- src/.  Does not postulate.  `swo-rank` is NOT restored.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-559.Probe559 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

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
open import L.Coding.Model {ℓ}
  using ( domAt; domAt-intro; prAtL; prAtL-adequate; prʟ; prʟ-fst )
open import Cubical.Data.FinData using ( Fin; zero; suc )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
import Cubical.HITs.PropositionalTruncation as PT

import LJ-1-521.Probe521 {ℓ} lem as P521
import LJ-1-537.Probe537 {ℓ} lem as P537

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- SHIFTS.  [LJ-1.497]'s (Probe497.agda:55-63), as [LJ-1.521] carries them
-- (Probe521.agda:88-96).  Rebuilt in two lines because [LJ-1.521] keeps
-- them `private` and section 5 must name the same de Bruijn index the
-- formula was written at.
private
  s3 : ∀ {n} → Fin n → Fin (suc (suc (suc n)))
  s3 i = suc (suc (suc i))

-- =====================================================================
-- 1.  THE RE-BASED BOUND.  [LJ-1.529]'s section 1
--     (agents/tasks/LJ-1-529/Probe529.agda:101-131), which is itself
--     [LJ-1.490]'s `Bound` (Probe490.agda:211-242) with `P521.swo-rank′`
--     where [LJ-1.490] has `swo-rank`, the rank [LJ-1.497] refuted.
--     REBUILT and not imported, because the brief forbids importing the
--     conjunct probes.
--
--     THIS CONJUNCT NEEDS THE BOUND AND `svAt` DID NOT.  [LJ-1.524] left
--     `bnd` free and said so (Probe524.agda:181-186).  Here the backward
--     implication must put a pair INTO the carve, and a separation only
--     admits what its bound already holds, so a free `bnd` makes the
--     obligation FALSE: at `bnd` empty the carve is empty and no `x ∈ a`
--     has an entry.  `below` is the fact that closes that gap.
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

-- =====================================================================
-- 2.  THE CARVE.  [LJ-1.490]'s (Probe490.agda:105-116) at [LJ-1.521]'s
--     `rankFo`.  BOTH readings are taken, and that is new: the three
--     sibling conjuncts took `rank-graph-out` alone.
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

rank-graph-in :
    (Q a bnd z : S)
  → ⟨ z ∈ˢ bnd ⟩ → ⟨ (z ∷ []) ⊨ P521.rankFo Q a ⟩
  → ⟨ z ∈ˢ fst (rank-graph Q a bnd) ⟩
rank-graph-in Q a bnd z hb hs =
  subst ⟨_⟩ (sym (snd (rank-graph Q a bnd) z)) (hb , hs)

-- =====================================================================
-- 3.  `Q` IS INSTANTIATED AND NOT HYPOTHESISED.  [LJ-1.524]'s
--     (Probe524.agda:106-115).
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
--     drift (src/L/Cardinal.lagda.md:223-228).
-- =====================================================================

DomAtOf : S → S → Type (ℓ-suc ℓ)
DomAtOf F a = ⟨ (F ∷ a ∷ []) ⊨ domAt zero (suc zero) ⟩

domAt-is-second-of-InjCode : (F a b : S) → InjCode F a b → DomAtOf F a
domAt-is-second-of-InjCode F a b h = h .snd .fst

-- =====================================================================
-- 5.  THE WRITING DIRECTION, AND IT IS THE PART NO PREDECESSOR BUILT.
--
--     `rankFo-adequate′` (Probe521.agda:1006-1012) READS a satisfaction
--     and returns the pair's shape.  Nothing in the tree goes the other
--     way, and the backward implication of `domAt` needs exactly that:
--     at a member `m` of `a`, the pair `(m , rank-at′ a oa m mx)` must
--     SATISFY `rankFo`.
--
--     `rankFo` is four nested existentials over one conjunction
--     (Probe521.agda:493-501), and `rankFo-adequate′` names their
--     witnesses in the order `q`, `m`, `r`, `f` (Probe521.agda:1013-1021).
--     Three of the four are already determined here: `q` is the
--     instantiated `Q`, so its equation is `refl`; `m` and `r` are the
--     member and its rank.  The FOURTH, the approximating function `f`,
--     is [LJ-1.537]'s `approx-carve`, whose three components are exactly
--     the three conjuncts of the innermost body.
-- =====================================================================

module Write (a : S) (oa : IsOrd (fst a)) (m : S) (mx : ⟨ fst m ∈ fst a ⟩) where

  Q : S
  Q = ordQ a oa

  r : S
  r = P521.rank-at′ a oa m mx

  z : S
  z = prʟ m r

  ap : Σ[ f ∈ S ] P537.Approximates a oa m mx f
  ap = P537.approx-carve a oa m mx

  -- the pair slot: `z` IS the pair of the member and its rank
  hpr : ⟨ (r ∷ m ∷ Q ∷ z ∷ []) ⊨ prAtL (s3 zero) (suc zero) zero ⟩
  hpr = subst ⟨_⟩
    (sym (prAtL-adequate (s3 zero) (suc zero) zero (r ∷ m ∷ Q ∷ z ∷ [])))
    (prʟ-fst m r)

  sat : ⟨ (z ∷ []) ⊨ P521.rankFo Q a ⟩
  sat = PT.∣ Q , (refl , PT.∣ m , PT.∣ r ,
          (hpr , (mx , PT.∣ ap .fst ,
            ( ap .snd .fst
            , ( ap .snd .snd .fst
              , ap .snd .snd .snd ) ) ∣₁)) ∣₁ ∣₁) ∣₁

-- =====================================================================
-- 6.  THE CARVE, AND THE TWO IMPLICATIONS OVER IT.
--
--     ONE NAME FOR THE CARVE AND NOWHERE ITS BODY.  This is [LJ-1.524]'s
--     price finding (Probe524.agda:160-171) and it is obeyed here: `G`
--     below is the carve, EVERY type that mentions the carve says `G`,
--     and section 7's type says `Carve.G a oa` and not its body.  With
--     two spellings the elaborator compares two satisfaction predicates
--     at `domAt zero (suc zero)`, walks down to
--     `pr (fst x) (fst y) ∈ fst γ₀`, and unfolds `rank-graph`,
--     `hasSeparationL` and the presentation to put the right argument in
--     constructor form.
-- =====================================================================

module Carve (a : S) (oa : IsOrd (fst a)) where

  module B = Bound′ a oa

  Q : S
  Q = ordQ a oa

  G : S
  G = fst (rank-graph Q a B.bnd)

  Hold : S → S → Type (ℓ-suc ℓ)
  Hold x y = ⟨ pr (fst x) (fst y) ∈ fst G ⟩

  -- 6.1  READING, and it is [LJ-1.524]'s and [LJ-1.529]'s reading
  --      verbatim: `prʟ-fst` enters, `rank-graph-out` leaves with
  --      satisfaction, `adequate-at-witness` reads, `pr-inj` splits.

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

  -- the argument is the member, up to the carrier
  arg : (x y : S) (h : Hold x y) → fst x ≡ fst (read x y h .fst)
  arg x y h = pr-inj (read x y h .snd .snd) .fst

  -- 6.2  THE FORWARD IMPLICATION.  An entry at `x` puts `x` in `a`.
  --      The conclusion is an hProp, so the truncation eliminates.

  fwd : (x : S) → PT.∥ (Σ[ y ∈ S ] Hold x y) ∥₁ → ⟨ fst x ∈ fst a ⟩
  fwd x = PT.rec (snd (fst x ∈ fst a)) at
    where
    at : Σ[ y ∈ S ] Hold x y → ⟨ fst x ∈ fst a ⟩
    at (y , h) =
      subst (λ v → ⟨ v ∈ fst a ⟩) (sym (arg x y h)) (read x y h .snd .fst)

  -- 6.3  THE BACKWARD IMPLICATION, and it is this task's own work.
  --      The witness is the rank at `x`; `Write.sat` says the pair
  --      satisfies `rankFo`, and `B.below` says the bound holds it.
  --      `rank-at′-val` (Probe521.agda:438-442) is the one equation the
  --      seal exports, and it is what carries `B.below`'s `swo-rank′`
  --      onto `rank-at′`.

  rank-of : (x : S) → ⟨ fst x ∈ fst a ⟩ → S
  rank-of x xa = P521.rank-at′ a oa x xa

  inBnd : (x : S) (xa : ⟨ fst x ∈ fst a ⟩)
        → ⟨ prʟ x (rank-of x xa) ∈ˢ B.bnd ⟩
  inBnd x xa =
    subst (λ v → ⟨ v ∈ fst B.bnd ⟩)
      (sym (prʟ-fst x (rank-of x xa)
            ∙ cong (pr (fst x)) (P521.rank-at′-val a oa x xa)))
      (B.below x xa)

  entry : (x : S) (xa : ⟨ fst x ∈ fst a ⟩) → Hold x (rank-of x xa)
  entry x xa =
    subst (λ v → ⟨ v ∈ fst G ⟩) (prʟ-fst x (rank-of x xa))
      (rank-graph-in Q a B.bnd (prʟ x (rank-of x xa))
        (inBnd x xa)
        (Write.sat a oa x xa))

  bwd : (x : S) → ⟨ fst x ∈ fst a ⟩ → PT.∥ (Σ[ y ∈ S ] Hold x y) ∥₁
  bwd x xa = PT.∣ rank-of x xa , entry x xa ∣₁

  -- 6.4  the conjunct.  `domAt-intro` (src/L/Coding/Model.lagda.md:298-305)
  --      asks for exactly the two implications, at every `x`.

  thm : DomAtOf G a
  thm = domAt-intro zero (suc zero) (G ∷ a ∷ []) (λ x → fwd x , bwd x)

-- =====================================================================
-- 7.  THE OBLIGATION.
-- =====================================================================

domAt-at-carve :
    (a : S) (oa : IsOrd (fst a))
  → DomAtOf (Carve.G a oa) a
domAt-at-carve = Carve.thm

-- THE CARVE IS NOT EMPTY, AND THIS IS THE SENTENCE THAT SAYS SO.
-- `domAt` at an empty carve over an empty `a` is true and says nothing,
-- so the conjunct alone is not evidence that the coding leg has a table.
-- The backward implication of section 6.3 builds a real entry at every
-- member, and this exposes it under one name for the next brief.
carve-holds-the-rank-pair :
    (a : S) (oa : IsOrd (fst a)) (x : S) (xa : ⟨ fst x ∈ fst a ⟩)
  → ⟨ pr (fst x) (fst (P521.rank-at′ a oa x xa))
      ∈ fst (Carve.G a oa) ⟩
carve-holds-the-rank-pair = Carve.entry

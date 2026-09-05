{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.566]  `InjCode` ASSEMBLED: all four conjuncts as ONE value.
--
-- The obligation is `injcode-assembled`, section 9.  Section 0 is W3,
-- the frame question, and it is `runs/W3.agda`, `runs/Unify.agda`,
-- `runs/U1.agda` and `runs/U3.agda`.
--
-- =====================================================================
-- WHY THIS FILE REBUILDS THE CARVE INSTEAD OF IMPORTING THREE PROBES.
--
-- The brief expects the four conjuncts to be taken from four committed
-- probes and put in a tuple, and prices the risk at "one term's
-- elaboration and not the assembly".  W3 MEASURED THE OPPOSITE and the
-- report gives the numbers.  Three of the four conjuncts exist, at three
-- SPELLINGS of one carve: `[LJ-1.524]`, `[LJ-1.529]` and `[LJ-1.559]`
-- each rebuilt `rank-graph` (Probe524.agda:86, Probe529.agda:150,
-- Probe559.agda:146) and `ordQ`, and `[LJ-1.529]` and `[LJ-1.559]` each
-- carry their own `module Bound′` with byte-identical bodies
-- (Probe529.agda:101-131, Probe559.agda:108-137).
--
-- ASKING THE ELABORATOR TO IDENTIFY ANY TWO OF THOSE SPELLINGS DOES NOT
-- TERMINATE IN THE TIME AVAILABLE.  `runs/U1.agda` is one `refl` between
-- `[LJ-1.524]`'s carve and `[LJ-1.529]`'s at ONE shared bound: 240 s,
-- exit 142, killed by my own cap (`runs/u1.out`).  `runs/U3.agda` is one
-- `refl` between the two rebuilt BOUNDS alone, the narrowest site there
-- is: 240 s, exit 142 (`runs/u3.out`).  `runs/Unify.agda`, the three
-- together, ran 540 s and did not finish (`runs/unify-1.out`).
--
-- `[LJ-1.524]` PREDICTED THIS AND MEASURED IT AT ITS OWN SITE
-- (Probe524.agda:160-178): with two spellings of the carve in one file
-- it "did not finish in ten minutes", and "the SAME proof with one name
-- throughout is seconds", because `_⊨_` recurses on the formula and
-- `_∈_` must put its right argument in constructor form, which unfolds
-- `rank-graph`, `hasSeparationL` and the presentation.  That law is the
-- reason `[LJ-1.547]` timed out five times, and it is the reason this
-- file has ONE `rank-graph`, ONE `ordQ`, ONE `Bound′` and ONE `Carve`.
-- Every conjunct below is proved AT `G` and no type in this file names a
-- second spelling of it.
--
-- SO THE RE-BASING THE BRIEF PRICED IS NOT WHAT THIS TASK SPENT.  What
-- it spent is a re-proof of three conjuncts at one carve, and the three
-- proofs are the predecessors' own, moved and not reinvented.  Each
-- section says whose it is at `file:line`.
-- =====================================================================
--
-- WHAT IS IMPORTED, AND WHY EACH IMPORT IS SAFE.
--   * `P521`, for the sealed rank, `rankFo` and the adequacy.  Names no
--     carve.
--   * `P531`, for `rank-at′-inj` (Probe531.agda:185-189).  Names no
--     carve: it is a statement about `rank-at′` alone.  It is the one
--     predecessor conjunct-task whose delivered term survives this
--     file's rebuild, and it saves the 81 code lines `[LJ-1.531]`
--     measured.
--   * `P537`, for `approx-carve` (Probe537.agda:616-620).  Names no
--     carve of this kind.
-- `P524`, `P529` and `P559` are NOT imported, and W3 is why: every term
-- they export that this file could want is stated at their own spelling
-- of the carve, and importing it would reintroduce the comparison W3
-- measured as unpayable.
--
-- THE BRIEF'S TABLE SAYS `injAt` WAS BUILT BY `[LJ-1.531]` AND IS GO.
-- IT WAS NOT.  `[LJ-1.531]` says so itself: "`injAt` IS NOT BUILT"
-- (lj-1.531-report.md:34, and again Probe531.agda:52).  It delivered
-- `rank-at′-inj` and measured that `injAt` was then a composition of
-- delivered terms (runs/Coexist.agda).  Section 7.3 is that composition,
-- written for the first time: three path compositions over `read`, `val`,
-- `arg` and `P531.rank-at′-inj`, exactly as `[LJ-1.531]` predicted
-- (lj-1.531-report.md:240-248).
--
-- Nothing lands in src/.  Does not postulate.  `swo-rank`, the rank
-- `[LJ-1.497]` refuted, inhabits no term of this file.  `InjL` is not
-- formed, B10 is not touched and `PowerIntoSucc` is not touched.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-566.Probe566 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure; ↾-reflects )
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
  using ( svAt; svAt-in; domAt; domAt-intro
        ; prAtL; prAtL-adequate; prʟ; prʟ-fst )
open import L.Coding.Injection {ℓ} lem using ( injAt; injAt-in )
open import Cubical.Data.FinData using ( Fin; zero; suc )
open import Cubical.Foundations.Prelude using ( J )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
import Cubical.HITs.PropositionalTruncation as PT

import LJ-1-521.Probe521 {ℓ} lem as P521
import LJ-1-531.Probe531 {ℓ} lem as P531
import LJ-1-537.Probe537 {ℓ} lem as P537

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- SHIFTS.  `[LJ-1.559]`'s (Probe559.agda:88-90), which are
-- `[LJ-1.497]`'s (Probe497.agda:55-63) as `[LJ-1.521]` carries them.
private
  s3 : ∀ {n} → Fin n → Fin (suc (suc (suc n)))
  s3 i = suc (suc (suc i))

-- =====================================================================
-- 1.  THE BOUND.  `[LJ-1.529]`'s `Bound′` (Probe529.agda:101-131), which
--     `[LJ-1.559]` carries byte for byte (Probe559.agda:108-137).  It is
--     here and not imported because it must be the SAME definition the
--     carve below is separated over; W3 measured what happens when it is
--     not.
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
-- 2.  THE CARVE'S SEPARATION.  `[LJ-1.559]`'s section 2
--     (Probe559.agda:146-178).  BOTH readings, because `domAt` writes.
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
-- 3.  `Q` IS INSTANTIATED AND NOT HYPOTHESISED.  `[LJ-1.524]`'s
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
-- 4.  THE RANK IS INDIFFERENT TO BOTH ARGUMENTS THAT CAN DIFFER.
--     `[LJ-1.524]`'s (Probe524.agda:126-145).  THE MOTIVE DOES NOT NAME
--     THE PATH, and `[LJ-1.524]` measured the alternative at more than
--     ten minutes.  Only `svAt` consumes this.
-- =====================================================================

rank-at′-irr :
    (a : S) (oa : IsOrd (fst a)) (m m' : S) → m ≡ m'
  → (mx : ⟨ fst m ∈ fst a ⟩) (mx' : ⟨ fst m' ∈ fst a ⟩)
  → fst (P521.rank-at′ a oa m mx) ≡ fst (P521.rank-at′ a oa m' mx')
rank-at′-irr a oa m m' q = atSame q
  where
  Mot : (m'' : S) → m ≡ m'' → Type (ℓ-suc ℓ)
  Mot m'' _ =
      (u : ⟨ fst m ∈ fst a ⟩) (u' : ⟨ fst m'' ∈ fst a ⟩)
    → fst (P521.rank-at′ a oa m u) ≡ fst (P521.rank-at′ a oa m'' u')

  base : Mot m refl
  base u u' = cong (λ v → fst (P521.rank-at′ a oa m v))
                   (snd (fst m ∈ fst a) u u')

  atSame : {m'' : S} (p : m ≡ m'') → Mot m'' p
  atSame = J Mot base

-- =====================================================================
-- 5.  THE FOUR CONJUNCTS' TYPES, READ OUT OF `InjCode` SO THAT NOTHING
--     CAN DRIFT (src/L/Cardinal.lagda.md:223-228).  Each projection
--     below typechecks only if the alias IS that component, so the four
--     aliases are pinned to the definition and not to my transcription.
--     This is `[LJ-1.524]`'s device (Probe524.agda:154-155),
--     `[LJ-1.529]`'s (Probe529.agda:190-191) and `[LJ-1.559]`'s
--     (Probe559.agda:190-191), at all four components at once.
-- =====================================================================

SvAtOf : S → S → Type (ℓ-suc ℓ)
SvAtOf F a = ⟨ (F ∷ a ∷ []) ⊨ svAt zero ⟩

DomAtOf : S → S → Type (ℓ-suc ℓ)
DomAtOf F a = ⟨ (F ∷ a ∷ []) ⊨ domAt zero (suc zero) ⟩

InjAtOf : S → S → Type (ℓ-suc ℓ)
InjAtOf F a = ⟨ (F ∷ a ∷ []) ⊨ injAt zero ⟩

RangeOf : S → S → Type (ℓ-suc ℓ)
RangeOf F b = (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst F ⟩ → ⟨ fst y ∈ fst b ⟩

svAt-is-first-of-InjCode : (F a b : S) → InjCode F a b → SvAtOf F a
svAt-is-first-of-InjCode F a b = fst

domAt-is-second-of-InjCode : (F a b : S) → InjCode F a b → DomAtOf F a
domAt-is-second-of-InjCode F a b h = h .snd .fst

injAt-is-third-of-InjCode : (F a b : S) → InjCode F a b → InjAtOf F a
injAt-is-third-of-InjCode F a b h = h .snd .snd .fst

range-is-fourth-of-InjCode : (F a b : S) → InjCode F a b → RangeOf F b
range-is-fourth-of-InjCode F a b h = h .snd .snd .snd

-- AND THE CONVERSE READING, which is what section 9 must inhabit.  Four
-- pieces at ONE `F` and ONE `b` ARE an `InjCode`, definitionally.
injcode-in :
    (F a b : S)
  → SvAtOf F a → DomAtOf F a → InjAtOf F a → RangeOf F b
  → InjCode F a b
injcode-in F a b sv dm ij rn = sv , dm , ij , rn

-- =====================================================================
-- 6.  THE WRITING DIRECTION, which only `domAt` needs.  `[LJ-1.559]`'s
--     section 5 (Probe559.agda:212-237), verbatim.  It is the part no
--     predecessor before `[LJ-1.559]` had, and it names no carve, so it
--     moves here unchanged.
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
-- 7.  THE CARVE, AND ALL FOUR CONJUNCTS OVER IT.
--
--     ONE NAME FOR THE CARVE AND NOWHERE ITS BODY.  `[LJ-1.524]`'s
--     measured design law (Probe524.agda:160-178), and this file is the
--     place it finally has to hold across four proofs at once: `G` below
--     is the carve, `C` is the codomain, and every type in sections 7,
--     8 and 9 says the name.
--
--     THE READING IS WRITTEN ONCE AND SPENT FOUR TIMES.  Each of the
--     three predecessors carries its own copy of `sat`/`read`/`val`
--     because each was alone in its file; here they are one block and
--     the four conjuncts are four consumers of it.  That is the whole
--     economy of assembling at one frame rather than four.
-- =====================================================================

module Carve (a : S) (oa : IsOrd (fst a)) where

  module B = Bound′ a oa

  Q : S
  Q = ordQ a oa

  C : S
  C = B.C

  G : S
  G = fst (rank-graph Q a B.bnd)

  Hold : S → S → Type (ℓ-suc ℓ)
  Hold x y = ⟨ pr (fst x) (fst y) ∈ fst G ⟩

  -- 7.0  THE READING, SHARED.  `[LJ-1.524]`'s (Probe524.agda:206-228),
  --      which `[LJ-1.529]` (Probe529.agda:233-251) and `[LJ-1.559]`
  --      (Probe559.agda:270-286) each repeat.  `prʟ-fst` enters,
  --      `rank-graph-out` leaves with satisfaction,
  --      `adequate-at-witness` reads, `pr-inj` splits.

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

  -- the argument is the member.  `[LJ-1.524]` named this `arg`
  -- (Probe524.agda:221-222); `[LJ-1.529]` exposed only `val` and
  -- `[LJ-1.531]` flagged the gap (lj-1.531-report.md:249-254).
  arg : (x y : S) (h : Hold x y) → fst x ≡ fst (read x y h .fst)
  arg x y h = pr-inj (read x y h .snd .snd) .fst

  -- the value is the rank at that member
  val : (x y : S) (h : Hold x y)
      → fst y ≡ fst (P521.rank-at′ a oa (read x y h .fst)
                                        (read x y h .snd .fst))
  val x y h = pr-inj (read x y h .snd .snd) .snd

  -- 7.1  `svAt`.  `[LJ-1.524]`'s section 5.2 and 5.3
  --      (Probe524.agda:230-255).

  same : (x y y' : S) (h : Hold x y) (h' : Hold x y')
       → read x y h .fst ≡ read x y' h' .fst
  same x y y' h h' =
    ↾-reflects {𝒮 = 𝒮ᵥ} {M = isL} (sym (arg x y h) ∙ arg x y' h')

  agree : (x y y' : S) (h : Hold x y) (h' : Hold x y')
        → fst (P521.rank-at′ a oa (read x y h .fst) (read x y h .snd .fst))
        ≡ fst (P521.rank-at′ a oa (read x y' h' .fst)
                                  (read x y' h' .snd .fst))
  agree x y y' h h' =
    rank-at′-irr a oa (read x y h .fst) (read x y' h' .fst)
      (same x y y' h h') (read x y h .snd .fst) (read x y' h' .snd .fst)

  sv : (x y y' : S) → Hold x y → Hold x y' → fst y ≡ fst y'
  sv x y y' h h' = val x y h ∙ agree x y y' h h' ∙ sym (val x y' h')

  thm-svAt : SvAtOf G a
  thm-svAt = svAt-in zero (G ∷ a ∷ []) sv

  -- 7.2  THE RANGE CLAUSE.  `[LJ-1.529]`'s section 5.2 and 5.3
  --      (Probe529.agda:253-273).  `rank-at′-val` is the one equation
  --      the seal exports and `pack`'s third component is the
  --      membership; both are at `B.w`, the record `rank-at′` runs on.

  rank-in-C : (m : S) (mx : ⟨ fst m ∈ fst a ⟩)
            → ⟨ fst (P521.rank-at′ a oa m mx) ∈ fst C ⟩
  rank-in-C m mx =
    subst (λ v → ⟨ v ∈ fst C ⟩)
      (sym (P521.rank-at′-val a oa m mx))
      (B.pack .snd .snd (fiber (fst a) mx .fst))

  ran : RangeOf G C
  ran x y h =
    subst (λ v → ⟨ v ∈ fst C ⟩) (sym (val x y h))
      (rank-in-C (read x y h .fst) (read x y h .snd .fst))

  -- 7.3  `injAt`, AND IT IS BUILT HERE FOR THE FIRST TIME.
  --      `[LJ-1.531]` delivered `rank-at′-inj` and measured that the
  --      rest was a composition of delivered terms, without writing it
  --      (lj-1.531-report.md:207-254).  This is that composition, and it
  --      is the three path compositions `[LJ-1.531]` predicted:
  --      two `val`s meet at `fst y` and feed the injectivity, which
  --      gives `fst m ≡ fst m'`; the two `arg`s carry it out to `x` and
  --      `x'`.  No new lemma.

  inj : (y x x' : S) → Hold x y → Hold x' y → fst x ≡ fst x'
  inj y x x' h h' =
    arg x y h ∙ members ∙ sym (arg x' y h')
    where
    ranks : fst (P521.rank-at′ a oa (read x y h .fst) (read x y h .snd .fst))
          ≡ fst (P521.rank-at′ a oa (read x' y h' .fst)
                                    (read x' y h' .snd .fst))
    ranks = sym (val x y h) ∙ val x' y h'

    members : fst (read x y h .fst) ≡ fst (read x' y h' .fst)
    members =
      P531.rank-at′-inj a oa (read x y h .fst) (read x' y h' .fst)
        (read x y h .snd .fst) (read x' y h' .snd .fst) ranks

  thm-injAt : InjAtOf G a
  thm-injAt = injAt-in zero (G ∷ a ∷ []) inj

  -- 7.4  `domAt`.  `[LJ-1.559]`'s section 6.2, 6.3 and 6.4
  --      (Probe559.agda:288-330).  The backward implication is the half
  --      no predecessor before `[LJ-1.559]` had.

  fwd : (x : S) → PT.∥ (Σ[ y ∈ S ] Hold x y) ∥₁ → ⟨ fst x ∈ fst a ⟩
  fwd x = PT.rec (snd (fst x ∈ fst a)) at
    where
    at : Σ[ y ∈ S ] Hold x y → ⟨ fst x ∈ fst a ⟩
    at (y , h) =
      subst (λ v → ⟨ v ∈ fst a ⟩) (sym (arg x y h)) (read x y h .snd .fst)

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

  thm-domAt : DomAtOf G a
  thm-domAt = domAt-intro zero (suc zero) (G ∷ a ∷ []) (λ x → fwd x , bwd x)

-- =====================================================================
-- 8.  THE FOUR, SEPARATELY, AT ONE FRAME.  Each is one name for section
--     7's field, so that a reader and the next brief can cite the
--     conjunct without opening the module, and so that a bisection has
--     four places to cut.
-- =====================================================================

svAt-at-carve : (a : S) (oa : IsOrd (fst a)) → SvAtOf (Carve.G a oa) a
svAt-at-carve = Carve.thm-svAt

domAt-at-carve : (a : S) (oa : IsOrd (fst a)) → DomAtOf (Carve.G a oa) a
domAt-at-carve = Carve.thm-domAt

injAt-at-carve : (a : S) (oa : IsOrd (fst a)) → InjAtOf (Carve.G a oa) a
injAt-at-carve = Carve.thm-injAt

range-at-carve :
    (a : S) (oa : IsOrd (fst a)) → RangeOf (Carve.G a oa) (Carve.C a oa)
range-at-carve = Carve.ran

-- =====================================================================
-- 9.  THE OBLIGATION.  ONE TERM THAT IS AN `InjCode`.
--
--     `F` is the carve, `a` is the ordinal, and `b` is `C`, the
--     bounding ordinal the pack forms.  `[LJ-1.529]` is the only
--     predecessor that named a `b` at all, and this is its `b`.
-- =====================================================================

injcode-assembled :
    (a : S) (oa : IsOrd (fst a))
  → InjCode (Carve.G a oa) a (Carve.C a oa)
injcode-assembled a oa =
  injcode-in (Carve.G a oa) a (Carve.C a oa)
    (svAt-at-carve a oa)
    (domAt-at-carve a oa)
    (injAt-at-carve a oa)
    (range-at-carve a oa)

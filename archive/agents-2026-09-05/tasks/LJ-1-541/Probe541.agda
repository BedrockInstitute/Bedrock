{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.541]  `domAt`, the FOURTH and last of the four `InjCode`
-- conjuncts, over the rank carve, with `Q` INSTANTIATED.
--
-- The obligation is `domAt-at-carve`, section 6.  Section 3 is W3, the
-- environment match, written FIRST and typechecked ALONE
-- (agents/tasks/LJ-1-541/runs/W3.agda, runs/w3-1.out to w3-3.out).
--
-- THE BRIEF'S ONE CONTRADICTION, DECLARED.  The brief says "DO NOT
-- REBUILD `approx-carve`, `rank-bound′` OR `rankFo`.  All three are
-- delivered in predecessors' probes.  Rebuild at their delivered types;
-- do not import a probe."  The last two clauses cannot both be obeyed:
-- `approx-carve` is 633 lines (Probe537.agda) over `rankFo`'s 1176
-- (Probe521.agda), the brief's own estimate for this file is about 220
-- lines, and a REBUILT `rankFo` would state the obligation at a
-- DIFFERENT formula, which is the drift `[LJ-1.537]` built
-- `runs/Pin.agda` to rule out.  So this file IMPORTS, which is what the
-- first clause orders and what every predecessor on this leg did
-- (Probe524.agda:20-32, Probe529.agda:16-30, and `[LJ-1.537]`'s report,
-- section "THE IMPORT OF A PREDECESSOR PROBE").  `bedrock.agda-lib:2`
-- lists `agents/tasks` as an include root.  The report carries this as a
-- finding against the brief and not as a silent adapter.
--
-- WHAT IS IMPORTED AND WHY EACH IS FORCED:
--   * `[LJ-1.521]`  the formula `rankFo`, the rank `rank-at′` with its one
--     exported equation `rank-at′-val`, and the `Q` witness.  A rebuild
--     would state the obligation at a different `rankFo`.
--   * `[LJ-1.529]`  the carve `rank-graph`, the re-based bound `Bound′`,
--     and the adequacy at the instantiated `Q`.
--   * `[LJ-1.537]`  `approx-carve`, passed WHOLE into section 3 so that
--     nothing here can re-spell its environment.
--
-- ONE MEASURED WALL, AND IT SHAPES THE WHOLE FILE.  `[LJ-1.524]` measured
-- that two spellings of the carve do not finish (lj-1.524-report.md,
-- section 3).  THIS FILE SHARPENS THAT LAW TO ONE DELTA, and section 4
-- carries the four runs.  `P529.Carve.G a oa` is NOT usable here: it is
-- the same set as this file's `G`, and Agda cannot say so.  So `G` below
-- is `fst (P529.rank-graph Q a bnd)`, which is `[LJ-1.529]`'s own shape,
-- and the reading is rebuilt at it (section 4.2, twelve lines) rather
-- than taken from `P529.Carve.read`.
--
-- NOTHING LANDS IN src/.  DOES NOT POSTULATE.  `InjCode` IS NOT BUILT and
-- `injAt` IS NOT ATTEMPTED: AD12 gives this brief one obligation.
-- `svAt`, the range clause and `rank-at′-inj` are NOT rebuilt.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-541.Probe541 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( var; con; _≐_ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; pr-inj )
open import V.Presentation {ℓ} using ( fiber )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; IsOrd )
open import L.Cardinal {ℓ} lem using ( InjCode )
open import L.Coding.Model {ℓ}
  using ( prʟ; prʟ-fst; prAtL; prAtL-adequate; domAt; domAt-intro )
open import Cubical.Data.FinData using ( Fin; zero; suc )
open import Cubical.Functions.Logic using ( ∃[∶]-syntax )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
import Cubical.HITs.PropositionalTruncation as PT

import LJ-1-521.Probe521 {ℓ} lem as P521
import LJ-1-529.Probe529 {ℓ} lem as P529
import LJ-1-537.Probe537 {ℓ} lem as P537

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

private
  s2 : ∀ {n} → Fin n → Fin (suc (suc n))
  s2 i = suc (suc i)
  s3 : ∀ {n} → Fin n → Fin (suc (suc (suc n)))
  s3 i = suc (suc (suc i))

-- =====================================================================
-- 1.  D-10, MECHANISED.  The brief orders every piece `[LJ-1.537]` names
--     checked at its `file:line` BEFORE any Agda, and `[LJ-1.537]` states
--     the composition "as a reading of the types and not as a
--     measurement".  Each name below is a TYPE ASCRIPTION over a
--     delivered term, transcribed from the predecessor's own report.  A
--     drift between a report and the tree is then a type error in THIS
--     file, and not a sentence anybody has to believe.
--
--     None of the six is re-proved.  Every right-hand side is one name.
--     They cost 1.77 s together (runs/BisA.agda, runs/bisA.out).
-- =====================================================================

-- (i)  the pair splits.  src/L/Coding/Model.lagda.md:329-330.
piece-pr : (x y : S) → fst (prʟ x y) ≡ pr (fst x) (fst y)
piece-pr = prʟ-fst

-- (ii)  the `Q` witness, INSTANTIATED and not hypothesised.
--       agents/tasks/LJ-1-521/Probe521.agda:1162-1164.
piece-Q : (a : S) (oa : IsOrd (fst a))
        → Σ[ Q ∈ S ] P521.ord-reads-Q Q a oa
piece-Q = P521.ord-set-witness

-- (iii)  the rank's one exported equation.
--        agents/tasks/LJ-1-521/Probe521.agda:438-442.
piece-val :
    (a : S) (oa : IsOrd (fst a)) (m : S) (mx : ⟨ fst m ∈ fst a ⟩)
  → fst (P521.rank-at′ a oa m mx)
    ≡ P521.swo-rank′ (P521.OrdSWO∈ₛ.w (fst a) oa) (fiber (fst a) mx .fst)
piece-val = P521.rank-at′-val

-- (iv)  the bound half.  agents/tasks/LJ-1-529/Probe529.agda:133-140.
piece-bound :
    (a : S) (oa : IsOrd (fst a))
  → Σ[ bnd ∈ S ]
      ((m : S) (mx : ⟨ fst m ∈ fst a ⟩)
        → ⟨ pr (fst m) (P521.swo-rank′ (P521.OrdSWO∈ₛ.w (fst a) oa)
                                       (fiber (fst a) mx .fst))
            ∈ fst bnd ⟩)
piece-bound = P529.rank-bound′

-- (v)  the satisfaction half's fourth existential.
--      agents/tasks/LJ-1-537/Probe537.agda:616-620.
piece-approx :
    (a : S) (oa : IsOrd (fst a)) (m : S) (mx : ⟨ fst m ∈ fst a ⟩)
  → Σ[ f ∈ S ] P537.Approximates a oa m mx f
piece-approx = P537.approx-carve

-- (vi)  the reading, which is `domAt`'s FIRST direction.  `[LJ-1.524]`
--       built it (lj-1.524-report.md:277) and `[LJ-1.529]` carried it to
--       the RE-BASED bound (Probe529.agda:239-246).  IT IS DELIVERED AND
--       THIS FILE CANNOT APPLY IT: its type says `P529.Carve.G a oa`, and
--       section 4 measures that no term of this file can be compared with
--       that name.  Section 4.2 rebuilds it in twelve lines instead.
piece-read :
    (a : S) (oa : IsOrd (fst a)) (x y : S)
  → ⟨ pr (fst x) (fst y) ∈ fst (P529.Carve.G a oa) ⟩
  → Σ[ m ∈ S ] Σ[ mx ∈ ⟨ fst m ∈ fst a ⟩ ]
      (pr (fst x) (fst y) ≡ pr (fst m) (fst (P521.rank-at′ a oa m mx)))
piece-read = P529.Carve.read

-- =====================================================================
-- 2.  THE CONJUNCT'S TYPE, read out of `InjCode` so that nothing can
--     drift (src/L/Cardinal.lagda.md:223-228).  `domAt zero (suc zero)`
--     at `(F ∷ a ∷ [])` reads slot 0 as the graph and slot 1 as the
--     domain, and the projection below typechecks only if `DomAtOf` is
--     definitionally the SECOND component there.
-- =====================================================================

DomAtOf : S → S → Type (ℓ-suc ℓ)
DomAtOf F a = ⟨ (F ∷ a ∷ []) ⊨ domAt zero (suc zero) ⟩

domAt-is-second-of-InjCode : (F a b : S) → InjCode F a b → DomAtOf F a
domAt-is-second-of-InjCode F a b h = h .snd .fst

-- =====================================================================
-- 3.  W3, THE ENVIRONMENT MATCH.  This is runs/W3.agda, repeated here
--     because a file cannot import the slice it was cut from.
--
--     `rankFo Q a` (Probe521.agda:493-501) at `(z ∷ [])` is
--
--       ∃ q. q ≐ Q ∧ ∃ m. ∃ r. ( prAtL z m r ∧ m ∈ a ∧ ∃ f. fn ∧ asg ∧ sup )
--
--     and at the innermost point the environment is
--     `(f ∷ r ∷ m ∷ q ∷ z ∷ [])`, which is `[LJ-1.521]`'s `Env.γ5`
--     (Probe521.agda:512-516).  `[LJ-1.537]` checked that environment in
--     a SIDE file against a hand-written telescope (runs/Pin.agda:46-62);
--     this section runs `approx-carve` INSIDE the formula itself.
--
--     THE MATCH IS EXACT AND NO ADAPTER EXISTS.  Every slot is filled by
--     a delivered term at its delivered spelling, and the carve is passed
--     WHOLE.  Green at the first attempt, 1.44 s.
-- =====================================================================

module Sat (a : S) (oa : IsOrd (fst a)) (x : S) (xa : ⟨ fst x ∈ fst a ⟩)
  where

  -- slot q.  `[LJ-1.537]`'s `Qwit` (Probe537.agda:581-582), same term.
  Q : S
  Q = P521.ord-set-witness a oa .fst

  -- slot r.
  r : S
  r = P521.rank-at′ a oa x xa

  -- slot z.  `[LJ-1.537]`'s `Zof` (Probe537.agda:584-585), same term.
  z : S
  z = prʟ x r

  -- the first conjunct at `q := Q`: `refl`.  `≈ˢ` on the model is
  -- `λ u v → fst u ≈ˢ fst v` (src/FOL/ZFStructure.lagda.md:148) over
  -- `𝒮ᵥ`'s path equality (src/V/Hierarchy.lagda.md:82).
  qQ : ⟨ (Q ∷ z ∷ []) ⊨ (var zero ≐ con Q) ⟩
  qQ = refl

  -- the second conjunct: `prʟ-fst` through `prAtL-adequate`
  -- (src/L/Coding/Model.lagda.md:125-128).
  hpr : ⟨ (r ∷ x ∷ Q ∷ z ∷ []) ⊨ prAtL (s3 zero) (suc zero) zero ⟩
  hpr = subst ⟨_⟩
          (sym (prAtL-adequate (s3 zero) (suc zero) zero (r ∷ x ∷ Q ∷ z ∷ [])))
          (prʟ-fst x r)

  -- the third conjunct is `xa` itself; the fourth existential is
  -- `[LJ-1.537]`'s carve passed WHOLE, so no environment is re-spelled.
  sat : ⟨ (z ∷ []) ⊨ P521.rankFo Q a ⟩
  sat = PT.∣ Q , (qQ ,
          PT.∣ x ,
            PT.∣ r , (hpr , (xa , PT.∣ P537.approx-carve a oa x xa ∣₁)) ∣₁
          ∣₁) ∣₁

-- =====================================================================
-- 4.  THE CARVE, AT ONE DELTA.
--
--     `[LJ-1.524]` measured that two SPELLINGS of the carve do not finish
--     (lj-1.524-report.md, section 3: two runs killed at ten and at eight
--     minutes).  Its cure is stated as ONE NAME FOR THE CARVE.  That is
--     not enough across files, and this task measured the difference:
--
--       runs/BisE.agda  `G = fst (P529.rank-graph Q a bnd)` and the
--                       separation equation ascribed at `G`.
--                       1.74 s, exit 0 (runs/bisE.out).
--       runs/BisC.agda  the same file with ONE line changed,
--                       `G = P529.Carve.G a oa`.  Killed at 155.02 s
--                       (runs/bisC.out).  The whole of Probe541 as first
--                       written, over that name, was killed at 718.26 s
--                       (runs/stage-a.out).
--       runs/BisD.agda  the same, with `Q` and `bnd` taken from
--                       `P529.Carve` itself so that only the module
--                       projection separates the two bodies.  Killed at
--                       337.30 s (runs/bisD.out).  THE ARGUMENTS ARE NOT
--                       THE PROBLEM.
--       runs/BisF.agda  `refl : DomF.G a oa ≡ P529.Carve.G a oa`, the
--                       compare at `S` and not under `_∈_`.  Killed at
--                       334.56 s (runs/bisF.out).  THE TWO CARVES ARE THE
--                       SAME SET AND AGDA CANNOT SAY SO.
--       runs/PinBody.agda  the same wall inside THIS task's names, as
--                       soon as `G`'s arguments must be unfolded too.
--                       Killed at 321.49 s (runs/pin-body.out).
--
--     So `G` below is `[LJ-1.529]`'s own shape and not its name, and
--     `Gmem` is one delta from it.  Every type in sections 4.2, 5 and 6
--     says `G`.
-- =====================================================================

module Dom (a : S) (oa : IsOrd (fst a)) where

  -- `[LJ-1.529]`'s `ordQ` (Probe529.agda:169-170) is this same term, so
  -- the spelling here is `[LJ-1.521]`'s and `[LJ-1.537]`'s, one delta
  -- from `[LJ-1.529]`'s, exactly as `[LJ-1.529]` pays internally.
  Q : S
  Q = P521.ord-set-witness a oa .fst

  bnd : S
  bnd = P529.Bound′.bnd a oa

  G : S
  G = fst (P529.rank-graph Q a bnd)

  Gmem : (w : S)
       → (w ∈ˢ G) ≡ ((w ∈ˢ bnd) ⊓ ((w ∷ []) ⊨ P521.rankFo Q a))
  Gmem = snd (P529.rank-graph Q a bnd)

  into : (w : S) → ⟨ w ∈ˢ bnd ⟩ → ⟨ (w ∷ []) ⊨ P521.rankFo Q a ⟩
       → ⟨ w ∈ˢ G ⟩
  into w hb hs = subst ⟨_⟩ (sym (Gmem w)) (hb , hs)

  outof : (w : S) → ⟨ w ∈ˢ G ⟩ → ⟨ (w ∷ []) ⊨ P521.rankFo Q a ⟩
  outof w h = subst ⟨_⟩ (Gmem w) h .snd

  -- ---------------------------------------------------------------
  -- 4.1  THE BOUND HALF.  `[LJ-1.529]`'s `below` is stated at
  --      `swo-rank′ w (fiber (fst a) mx .fst)`; `rank-at′-val`
  --      (Probe521.agda:438-442) is the equation that carries it to
  --      `rank-at′`.  This is `[LJ-1.529]`'s own step for `rank-in-C`
  --      (Probe529.agda:260-266), at the bound instead of the codomain.
  -- ---------------------------------------------------------------

  module Pt (x : S) (xa : ⟨ fst x ∈ fst a ⟩) where

    open module S′ = Sat a oa x xa public using ( r; z; sat )

    atRank : ⟨ pr (fst x) (fst r) ∈ fst bnd ⟩
    atRank = subst (λ v → ⟨ pr (fst x) v ∈ fst bnd ⟩)
               (sym (P521.rank-at′-val a oa x xa))
               (P529.Bound′.below a oa x xa)

    inBnd : ⟨ z ∈ˢ bnd ⟩
    inBnd = subst (λ v → ⟨ v ∈ fst bnd ⟩) (sym (prʟ-fst x r)) atRank

    -- the pair is IN the carve: the bound half and the satisfaction half
    -- meet at the separation equation and nowhere else.
    inG : ⟨ pr (fst x) (fst r) ∈ fst G ⟩
    inG = subst (λ v → ⟨ v ∈ fst G ⟩) (prʟ-fst x r) (into z inBnd sat)

  -- ---------------------------------------------------------------
  -- 4.2  THE READING, REBUILT.  This is `P529.Carve.sat` and
  --      `P529.Carve.read` (Probe529.agda:233-246) with `G` in place of
  --      `Carve.G`, and nothing else changed.  It is rebuilt and not
  --      imported for the measured reason in section 4, and the twelve
  --      lines are the price of that wall.
  -- ---------------------------------------------------------------

  read : (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst G ⟩
       → Σ[ m ∈ S ] Σ[ mx ∈ ⟨ fst m ∈ fst a ⟩ ]
           (pr (fst x) (fst y) ≡ pr (fst m) (fst (P521.rank-at′ a oa m mx)))
  read x y h = t .fst , (t .snd .fst , sym (prʟ-fst x y) ∙ t .snd .snd)
    where
    inG : ⟨ prʟ x y ∈ˢ G ⟩
    inG = subst (λ v → ⟨ v ∈ fst G ⟩) (sym (prʟ-fst x y)) h
    t = P529.adequate-at-witness a oa (prʟ x y) (outof (prʟ x y) inG)

  -- ---------------------------------------------------------------
  -- 5.  THE TWO DIRECTIONS.
  -- ---------------------------------------------------------------

  -- 5.1  out of the carve, into the domain.  `pr-inj`
  --      (src/V/Coding.lagda.md:178-179) splits the pair the reading
  --      returns, and the member's own membership is the conclusion.
  fwd : (x : S) → ⟨ ∃[ y ∶ S ] (pr (fst x) (fst y) ∈ fst G) ⟩
      → ⟨ fst x ∈ fst a ⟩
  fwd x = PT.rec (snd (fst x ∈ fst a)) at
    where
    at : Σ[ y ∈ S ] ⟨ pr (fst x) (fst y) ∈ fst G ⟩ → ⟨ fst x ∈ fst a ⟩
    at (y , h) =
      subst (λ v → ⟨ v ∈ fst a ⟩) (sym (pr-inj (read x y h .snd .snd) .fst))
            (read x y h .snd .fst)

  -- 5.2  out of the domain, into the carve.  THE DIRECTION THAT WAS
  --      MISSING (src/L/Coding/Model.lagda.md:294-296).  The witness is
  --      the rank at the member and nothing else was ever a candidate.
  bwd : (x : S) → ⟨ fst x ∈ fst a ⟩
      → ⟨ ∃[ y ∶ S ] (pr (fst x) (fst y) ∈ fst G) ⟩
  bwd x xa = PT.∣ Pt.r x xa , Pt.inG x xa ∣₁

  -- 5.3  `domAt-intro` (src/L/Coding/Model.lagda.md:298-305) takes the
  --      two directions and nothing else.
  thm : DomAtOf G a
  thm = domAt-intro zero (suc zero) (G ∷ a ∷ []) (λ x → fwd x , bwd x)

-- =====================================================================
-- 6.  THE OBLIGATION.  `Dom.G a oa` is `[LJ-1.529]`'s carve over the
--     re-based bound, written at its shape and not at its name for the
--     reason section 4 measured.
-- =====================================================================

domAt-at-carve : (a : S) (oa : IsOrd (fst a)) → DomAtOf (Dom.G a oa) a
domAt-at-carve = Dom.thm

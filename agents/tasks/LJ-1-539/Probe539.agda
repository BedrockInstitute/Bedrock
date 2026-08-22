{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.539] The subK family of TFacts, collected at KValue's frame.
--
-- W3 FIRST, and alone: WHICH SLOT-ONE FACT THE FAMILY WANTS.  Three are
-- built at this frame and the brief names all three: `valSub`
-- ([LJ-1.508], agents/tasks/LJ-1-508/Probe508.agda:201-205), `dK` and
-- `zK` ([LJ-1.530], agents/tasks/LJ-1-530/Probe530.agda:131 and :169).
-- `subK-gen` (src/L/Coding/EnvSupply.lagda.md:481-487) takes a
-- MEMBERSHIP `TK`, and [LJ-1.508] measured that `valSub` does NOT give
-- that membership back (Probe508.agda:237-243, the converse is FALSE at
-- this frame).  So the W3 question is not "does valSub give TK": it is
-- "does the FAMILY need TK at all".  The term below answers it.
--
-- This is the file at the W3 run.  The record, the frame and the witness
-- are appended after that run lands.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber,
-- set on the pane by the program and untouched here.  Nothing lands in
-- src/.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-539.Probe539 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; isTransV; IsOrd )
open import L.Axioms.Numerals {ℓ} using ( sucʟ; sucʟ-fst )
open import L.Coding.Model {ℓ}
  using ( prʟ; prʟ-fst; subValAt; subValAt-adequate
        ; subValSuccAt; subValSuccAt-adequate )
open import L.Coding.EnvSupply {ℓ} lem using ( module Fact )
open import L.Condensation {ℓ} lem using ( module KValue; module KFactsNS )
open import L.Condensation.TwelveAgree {ℓ} lem using ( TFacts )
open import Cubical.Data.Nat using ( ℕ; _+_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; ∅ )
open InfinitySet {ℓ} using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )
open KFactsNS
open KFacts

-- =====================================================================
-- W3.  `subK-gen`'s `TK` ARGUMENT, AT THE FRAME: FROM `valSub`.
--
--   `Sub K E` is [LJ-1.508]'s `valSub` shape, stated at a set E and not
--   at a slot (agents/tasks/LJ-1-508/Probe508.agda:146-147, and the
--   frame instance at :201-205).  It is KFacts's own shape for the
--   CARRIER slot (`carrierK`, src/L/Condensation.lagda.md:6113).
--
--   `subK-gen` (src/L/Coding/EnvSupply.lagda.md:481-487) spends its
--   `TK` in EXACTLY ONE place: it promotes the adequacy's Kuratowski
--   pair out of slot one and into K, through `Ktr`.  A SUBSET fact at
--   slot one does that promotion directly, so the family does not need
--   the membership.  Everything after the promotion is `Fact.prK`
--   (src/L/Coding/EnvSupply.lagda.md:452-459), the same delivered term
--   `subK-gen` itself spends.
--
--   THE COST OF THE WEAKER HYPOTHESIS IS THE PACKAGING.  `valSub`
--   quantifies over `S`; the adequacy pins a raw `V ℓ` pair.  `prʟ` and
--   `prʟ-fst` (src/L/Coding/Model.lagda.md:329) close that, and the
--   `where` block below is the whole of it.
-- =====================================================================

Sub : (K E : S) → Type (ℓ-suc ℓ)
Sub K E = (x : S) → ⟨ fst x ∈ fst E ⟩ → ⟨ fst x ∈ fst K ⟩

module W3 (K : S) (Ktr : isTransV (fst K)) where

  module F = Fact K Ktr

  -- The pair the adequacy pins, packaged back into `S`.
  keyPair : {n : ℕ} (γ : S ^ n) (ar a y : Fin n) → S
  keyPair γ ar a y = prʟ (prʟ (lookup ar γ) (lookup a γ)) (lookup y γ)

  keyEq : {n : ℕ} (γ : S ^ n) (ar a y : Fin n)
        → fst (keyPair γ ar a y)
          ≡ pr (pr (fst (lookup ar γ)) (fst (lookup a γ))) (fst (lookup y γ))
  keyEq γ ar a y =
    prʟ-fst (prʟ (lookup ar γ) (lookup a γ)) (lookup y γ)
    ∙ cong (λ u → pr u (fst (lookup y γ))) (prʟ-fst (lookup ar γ) (lookup a γ))

  -- THE W3 TERM.  `subK-gen`'s conclusion, from `valSub` in place of
  -- `TK`.  Generic in the environment length, the environment and all
  -- four indices, exactly as src/ states `subK-gen`.
  subK-from-sub : {n : ℕ} (γ : S ^ n) (T ar a y : Fin n)
                → Sub K (lookup T γ)
                → ⟨ γ ⊨ subValAt T ar a y ⟩
                → ⟨ fst (lookup y γ) ∈ fst K ⟩
  subK-from-sub γ T ar a y valSub h =
    F.prK (pr (fst (lookup ar γ)) (fst (lookup a γ))) (fst (lookup y γ))
      (subst (λ u → ⟨ u ∈ fst K ⟩) (keyEq γ ar a y)
        (valSub (keyPair γ ar a y)
          (subst (λ u → ⟨ u ∈ fst (lookup T γ) ⟩) (sym (keyEq γ ar a y))
            (subst ⟨_⟩ (subValAt-adequate T ar a y γ) h))))
      .snd

  -- The SIBLING, for the two fields whose adequacy is `subValSuccAt`.
  -- `subKSucc-gen` (src/L/Coding/EnvSupply.lagda.md:489-495) differs
  -- from `subK-gen` in the key alone: the arity is a SUCCESSOR.  The
  -- packaging grows by one `sucʟ` (src/L/Axioms/Numerals.lagda.md:104)
  -- and one `sucʟ-fst` (:152), and nothing else moves.
  keyPairS : {n : ℕ} (γ : S ^ n) (ar a y : Fin n) → S
  keyPairS γ ar a y =
    prʟ (prʟ (sucʟ (lookup ar γ)) (lookup a γ)) (lookup y γ)

  keyEqS : {n : ℕ} (γ : S ^ n) (ar a y : Fin n)
         → fst (keyPairS γ ar a y)
           ≡ pr (pr (sucV (fst (lookup ar γ))) (fst (lookup a γ)))
                (fst (lookup y γ))
  keyEqS γ ar a y =
    prʟ-fst (prʟ (sucʟ (lookup ar γ)) (lookup a γ)) (lookup y γ)
    ∙ cong (λ u → pr u (fst (lookup y γ)))
        ( prʟ-fst (sucʟ (lookup ar γ)) (lookup a γ)
        ∙ cong (λ u → pr u (fst (lookup a γ))) (sucʟ-fst (lookup ar γ)) )

  subKSucc-from-sub : {n : ℕ} (γ : S ^ n) (T ar a y : Fin n)
                    → Sub K (lookup T γ)
                    → ⟨ γ ⊨ subValSuccAt T ar a y ⟩
                    → ⟨ fst (lookup y γ) ∈ fst K ⟩
  subKSucc-from-sub γ T ar a y valSub h =
    F.prK (pr (sucV (fst (lookup ar γ))) (fst (lookup a γ)))
      (fst (lookup y γ))
      (subst (λ u → ⟨ u ∈ fst K ⟩) (keyEqS γ ar a y)
        (valSub (keyPairS γ ar a y)
          (subst (λ u → ⟨ u ∈ fst (lookup T γ) ⟩) (sym (keyEqS γ ar a y))
            (subst ⟨_⟩ (subValSuccAt-adequate T ar a y γ) h))))
      .snd

-- =====================================================================
-- THE FAMILY, WRITTEN ONCE AT `TFacts`'s OWN SHAPE (W2).
--
-- SEVEN FIELDS AND NOT SIX.  The brief counts six; `EnvSupply`'s own
-- comment counts seven (src/L/Coding/EnvSupply.lagda.md:480) and
-- `[LJ-1.509]`'s report already corrected the count
-- (agents/tasks/LJ-1-509/lj-1.509-report.md:212-217).  The seventh is
-- `subK-allin` (src/L/Condensation/TwelveAgree.lagda.md:326-331).  It
-- is in the family, it reads `T` out of the same cell, and the same one
-- hypothesis pays it, so leaving it out would have split the family for
-- nothing.
--
-- Copied verbatim from src/L/Condensation/TwelveAgree.lagda.md:265-288,
-- :290-295, :311-316 and :326-331.  The seven name only `K` and `γ'` of
-- that record's fifteen index parameters, so only those two are stated
-- here.  `statement-matches` below is Agda's word that these ARE the
-- record's own types.
-- =====================================================================

record SubKSeven {n : ℕ} (K : Fin (5 + n)) (γ' : S ^ (11 + n))
  : Type (ℓ-suc ℓ) where
  field
    subK₁-and : (x y yc b a ar c : S) → ⟨ (x ∷ y ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨
                  subValAt {7 + (11 + n)} (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
                           (suc (suc (suc (suc (suc zero)))))
                           (suc (suc (suc (suc zero))))
                           (suc zero) ⟩
                → ⟨ fst y ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
    subK₀-and : (y ya yc b a ar c : S) → ⟨ (y ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨
                  subValAt {7 + (11 + n)} (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
                           (suc (suc (suc (suc (suc zero)))))
                           (suc (suc (suc zero)))
                           zero ⟩
                → ⟨ fst y ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
    subK₁-imp : (E yb ya yc b a ar c : S) → ⟨ (E ∷ yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨
                  subValAt (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
                           (suc (suc (suc (suc (suc (suc zero))))))
                           (suc (suc (suc (suc (suc zero)))))
                           (suc (suc zero)) ⟩
                → ⟨ fst ya ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
    subK₀-imp : (E yb ya yc b a ar c : S) → ⟨ (E ∷ yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨
                  subValAt (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
                           (suc (suc (suc (suc (suc (suc zero))))))
                           (suc (suc (suc (suc zero))))
                           (suc zero) ⟩
                → ⟨ fst yb ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
    subK-neg : (ya yc a ar c E : S) → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ') ⊨
                 subValAt (suc (suc (suc (suc (suc (suc (suc zero)))))))
                          (suc (suc (suc (suc zero))))
                          (suc (suc (suc zero)))
                          (suc zero) ⟩
               → ⟨ fst ya ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
    subK-un : (ya yc a ar c E : S) → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ') ⊨
                subValSuccAt (suc (suc (suc (suc (suc (suc (suc zero)))))))
                             (suc (suc (suc (suc zero))))
                             (suc (suc (suc zero)))
                             (suc zero) ⟩
              → ⟨ fst ya ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
    subK-allin : (E ya yc b a ar c : S) → ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨
                   subValSuccAt (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
                                (suc (suc (suc (suc (suc zero)))))
                                (suc (suc (suc zero)))
                                (suc zero) ⟩
                 → ⟨ fst ya ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩

-- `SubKSeven` IS THE RECORD'S OWN BLOCK, AND AGDA SAYS SO.  Every field
-- below is read off a `TFacts` value by projection, with no coercion,
-- no `subst` and no re-association.  It certifies the STATEMENT only;
-- the obligation never calls it, and no `TFacts` field is used to prove
-- a `TFacts` field.  If a type here ever drifts from the master, this
-- term stops checking.

statement-matches : {n : ℕ}
    (N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K : Fin (5 + n))
    (γ' : S ^ (11 + n))
  → TFacts N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K γ'
  → SubKSeven {n} K γ'
statement-matches N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K γ' tf = record
  { subK₁-and  = TFacts.subK₁-and tf
  ; subK₀-and  = TFacts.subK₀-and tf
  ; subK₁-imp  = TFacts.subK₁-imp tf
  ; subK₀-imp  = TFacts.subK₀-imp tf
  ; subK-neg   = TFacts.subK-neg tf
  ; subK-un    = TFacts.subK-un tf
  ; subK-allin = TFacts.subK-allin tf }

-- =====================================================================
-- THE COLLECTED TELESCOPE, AT A GENERIC CARRIER (W2).
--
-- TWO HYPOTHESES PAY ALL SEVEN, AND NEITHER IS NEW MATHEMATICS.
--
--   `arity` is `KFacts.arityK`'s shape over `S`
--   (src/L/Condensation.lagda.md:6114-6115).  `[LJ-1.509]` measured that
--   asking a frame for `isTransV` instead is asking for more than the
--   frame delivers (agents/tasks/LJ-1-509/lj-1.509-report.md:180-184),
--   and `Ktr` below is that report's three-line bridge, re-written at
--   this site rather than imported (AGENTS.md:45).
--
--   `valSub` is `[LJ-1.508]`'s slot-one hypothesis
--   (agents/tasks/LJ-1-508/Probe508.agda:201-205), which that task
--   MEASURED to be strictly weaker than the membership `TK`
--   `[LJ-1.509]` took (Probe508.agda:237-243: the converse is refuted at
--   this frame).  `TK` still buys it, in one `arity` step, and
--   `sub-from-member` below is that step.  So this telescope is weaker
--   than `[LJ-1.509]`'s and it covers it.
--
-- EVERY FIELD IS ONE APPLICATION OF `W3.subK-from-sub` OR OF
-- `W3.subKSucc-from-sub`, AND NOTHING ELSE.  No `subst`, no weakening
-- and no second step at the field level: the packaging lives once, in
-- `W3`.  The index quadruples are the ones `EnvSupply`'s own delivered
-- instantiations already use (src/L/Coding/EnvSupply.lagda.md:506, :517,
-- :528, :539, :550, :561, :572); this module changes the environment
-- TAIL from `Vec S 2` to `γ'` and keeps every numeral.
-- =====================================================================

module Seven {n : ℕ} (K : Fin (5 + n)) (γ' : S ^ (11 + n))
  (arity : (N v : S) → ⟨ fst v ∈ fst N ⟩
         → ⟨ fst N ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
         → ⟨ fst v ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (valSub : (x : S) → ⟨ fst x ∈ fst (lookup (suc zero) γ') ⟩
          → ⟨ fst x ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  where

  Kset : S
  Kset = lookup (suc (suc (suc (suc (suc (suc K)))))) γ'

  -- [LJ-1.509]'s bridge, re-written here: a member of `fst Kset` is
  -- `isL` because `Kset` is, and a member of that member is `isL` again.
  Ktr : isTransV (fst Kset)
  Ktr {A} {u} u∈A A∈K = arity (A , isLA) (u , isL-trans u∈A isLA) u∈A A∈K
    where
    isLA : ⟨ isL A ⟩
    isLA = isL-trans A∈K (snd Kset)

  module E = W3 Kset Ktr

  -- THE OBLIGATION'S BODY.  The seven, collected.
  seven : SubKSeven {n} K γ'
  seven = record
    { subK₁-and = λ x y yc b a ar c h →
        E.subK-from-sub (x ∷ y ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ')
          (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
          (suc (suc (suc (suc (suc zero)))))
          (suc (suc (suc (suc zero))))
          (suc zero) valSub h
    ; subK₀-and = λ y ya yc b a ar c h →
        E.subK-from-sub (y ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ')
          (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
          (suc (suc (suc (suc (suc zero)))))
          (suc (suc (suc zero)))
          zero valSub h
    ; subK₁-imp = λ E' yb ya yc b a ar c h →
        E.subK-from-sub (E' ∷ yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ')
          (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
          (suc (suc (suc (suc (suc (suc zero))))))
          (suc (suc (suc (suc (suc zero)))))
          (suc (suc zero)) valSub h
    ; subK₀-imp = λ E' yb ya yc b a ar c h →
        E.subK-from-sub (E' ∷ yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ')
          (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
          (suc (suc (suc (suc (suc (suc zero))))))
          (suc (suc (suc (suc zero))))
          (suc zero) valSub h
    ; subK-neg = λ ya yc a ar c E' h →
        E.subK-from-sub (E' ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ')
          (suc (suc (suc (suc (suc (suc (suc zero)))))))
          (suc (suc (suc (suc zero))))
          (suc (suc (suc zero)))
          (suc zero) valSub h
    ; subK-un = λ ya yc a ar c E' h →
        E.subKSucc-from-sub (E' ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ')
          (suc (suc (suc (suc (suc (suc (suc zero)))))))
          (suc (suc (suc (suc zero))))
          (suc (suc (suc zero)))
          (suc zero) valSub h
    ; subK-allin = λ E' ya yc b a ar c h →
        E.subKSucc-from-sub (E' ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ')
          (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
          (suc (suc (suc (suc (suc zero)))))
          (suc (suc (suc zero)))
          (suc zero) valSub h }

  -- [LJ-1.509]'s `TK` BUYS THIS TELESCOPE'S `valSub`, in one `arity`
  -- step.  This is [LJ-1.508]'s `memberSubK` (Probe508.agda:162-163) at
  -- this site.  With the arrow measured only in this direction, the
  -- membership frame is the stronger one and the seven do not want it.
  sub-from-member :
      ⟨ fst (lookup (suc zero) γ') ∈ fst Kset ⟩
    → (x : S) → ⟨ fst x ∈ fst (lookup (suc zero) γ') ⟩ → ⟨ fst x ∈ fst Kset ⟩
  sub-from-member TK x hx = arity (lookup (suc zero) γ') x hx TK

-- =====================================================================
-- THE OBLIGATION, AT `KValue`'s FRAME.
--
-- `KValue` (src/L/Condensation.lagda.md:7380-7395) binds the carrier and
-- the stage and supplies ONE `KFacts` value, `facts` (:7411), over
-- `Kenv : S ^ 14`.  Six cons cells put it at `TFacts`'s lengths, which
-- is the frame `[LJ-1.495]` measured
-- (agents/tasks/LJ-1-495/lj-1.495-report.md:56-60): `S ^ 20` is
-- `S ^ (11 + 9)` and `Fin 14` is `Fin (5 + 9)`.
--
-- THE SIX CELLS STAY FREE.  `[LJ-1.538]` pinned cell 0 to `SupplyEnv`'s
-- `B₀` because the nine env forms read the carrier out of it
-- (agents/tasks/LJ-1-538/Probe538.agda:177-178).  THE SEVEN READ NO
-- CELL BUT SLOT ONE, so this frame pins nothing and `SupplyEnv` is not
-- opened at all.  That is why this telescope carries NO `ω∈σ`: it is
-- `KValue`'s seven parameters word for word, plus the slot-one fact.
--
-- `arityK` NEEDS NO `KFactsCons` HERE.  `[LJ-1.509]` measured that for
-- this field at this frame (agents/tasks/LJ-1-509/Probe509.agda:206-207,
-- lj-1.509-report.md:317-322) and AGENTS.md:45 forbids carrying a cure
-- by analogy, so the line below re-measures it: `facts .arityK` is
-- passed at the SHIFTED index with no conversion, and if the reduction
-- ever stops being definitional this file stops checking.
-- =====================================================================

module Frame
  (lam : V ℓ) (ordλ : IsOrd lam)
  (succλ : (d : V ℓ) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ lam ⟩)
  (gam : V ℓ) (ordγ : IsOrd gam) (γ∈λ : ⟨ gam ∈ lam ⟩) where

  open KValue lam ordλ succλ ∅∈λ gam ordγ γ∈λ

  γ★ : (c1 c2 c3 c4 c5 c6 : S) → S ^ 20
  γ★ c1 c2 c3 c4 c5 c6 = c6 ∷ c5 ∷ c4 ∷ c3 ∷ c2 ∷ c1 ∷ Kenv

  subK-frame-inhabited : (c1 c2 c3 c4 c5 c6 : S)
    → ( (x : S)
      → ⟨ fst x ∈ fst (lookup (suc zero) (γ★ c1 c2 c3 c4 c5 c6)) ⟩
      → ⟨ fst x ∈ fst (lookup (suc (suc (suc (suc (suc (suc iK))))))
                        (γ★ c1 c2 c3 c4 c5 c6)) ⟩ )
    → SubKSeven {9} iK (γ★ c1 c2 c3 c4 c5 c6)
  subK-frame-inhabited c1 c2 c3 c4 c5 c6 valSub =
    Seven.seven {9} iK (γ★ c1 c2 c3 c4 c5 c6) (facts .arityK) valSub

-- THE OBLIGATION AT THE TOP LEVEL: the collected telescope, then the
-- six free cells, then the slot-one fact, then the witness.
subK-frame-inhabited = Frame.subK-frame-inhabited

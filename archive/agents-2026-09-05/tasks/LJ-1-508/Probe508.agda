{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.508] valK and valK-un of TFacts, at KValue's frame.
--
-- valK (src/L/Condensation/TwelveAgree.lagda.md:173-176) is NOT a
-- decoder.  codesK reads a code apart; valK concludes a K membership
-- from a pair that sits in SLOT ONE, the value set.  So it is a
-- CLOSURE fact about slot one, and every dispatch before this one
-- asked about slot two.
--
-- THE FILE IN THE ORDER IT WAS BUILT.
--
--   1. W3, `valK-from-arityK`, obligation omitted, typechecked ALONE
--      first.  NO-GO, exit 42, and the error names the missing input:
--      `⟨ fst (prʟ c yc) ∈ fst (lookup K γ) ⟩`.  The W3-only file is
--      kept verbatim at runs/Probe508.w3-only.agda.txt.  Section 2 of
--      the report carries the error.  Below, the same fact is stated
--      GREEN as a refutation instead of as a failed typecheck.
--
--   2. `valK-bare-is-false`: the bare field, at KValue's own frame,
--      with the FULL KFacts value supplied, is refuted by a
--      counterexample.  The code is well formed and its arity IS a
--      numeral, so nothing here turns on junk in the code slot.  The
--      whole failure is slot one.
--
--      A PREDECESSOR REFUTED THE OLDER FIELD AND THIS IS NOT THAT
--      REFUTATION.  [LJ-1.151] and [LJ-1.153] measured the field FALSE
--      when `yc` occurred in NO premise
--      (agents/tasks/LJ-1-153/ProbeLJ1153A.agda:90-96, exit 0;
--      agents/tasks/LJ-1-151/lj-1.151-report.md:23).  The field was
--      then repaired: today it CARRIES the graph entry
--      (src/L/Condensation/TwelveAgree.lagda.md:175).  The
--      counterexample below SATISFIES that premise, so it refutes the
--      repaired field and not the old one.  AGENTS.md:45 says a
--      measured cure does not transfer by analogy, and this is the
--      re-measurement at the new site.
--
--      [LJ-1.151] also built the CURE, at a CONCRETE level: its
--      `Slots.frame-valK` takes the graph slot's MEMBERSHIP `TK` plus
--      a pin `Kis : lookup K γ' ≡ levelK α o`
--      (agents/tasks/LJ-1-151/ProbeLJ1151A.agda:100-112), and
--      [LJ-1.245] measured that its match claim RESTS on that pin
--      (agents/tasks/LJ-1-245/lj-1.245-report.md:333).  Nothing below
--      pins anything: `arityK` comes from KValue's own KFacts value.
--
--   3. The obligation, under the WEAKEST hypothesis that works:
--      slot one's members lie in K.  That is `carrierK`'s shape
--      (src/L/Condensation.lagda.md:6113) at slot one instead of at
--      the carrier slot.  The single-membership form implies it in
--      one arityK, and is stated separately so the report can say
--      which is weaker.
--
--   4. `Weak.subK-is-strictly-weaker`: WHICH of the two hypotheses is
--      weaker is measured, not argued.  The converse is refuted at
--      the bound itself.
--
--   5. `valSub-from-carrier`: a CONDITIONAL handed to [LJ-1.505],
--      which owns what occupies each front slot.  It pins nothing.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide
-- caliber, set on the pane by the program and untouched here.
-- Nothing lands in src/.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-508.Probe508 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import V.Model {ℓ} using ( self∈sucV )
open import V.Coding {ℓ} using ( pr )
open import FOL.ZFStructure using ( module hPropStructure )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; IsOrd )
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import L.Axioms.Numerals {ℓ}
  using ( numeralL; numeralL-fst; pairʟ; sucʟ; sucʟ-fst )
open import L.Coding.Model {ℓ} using ( prʟ; prʟ-fst )
open import L.Condensation {ℓ} lem
  using ( module KValue; module KFactsNS; module ChainZ )
open import Cubical.Data.Nat using ( ℕ; _+_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; ∅ )
open InfinitySet {ℓ} using ( #_; sucV )
import Cubical.Data.Empty as Empty

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ
open KFactsNS
open KFacts
module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL

-- =====================================================================
-- W2.  THE TWO FIELD TYPES, ONCE, at TFacts's own generic shape
--   (src/L/Condensation/TwelveAgree.lagda.md:129-131, :173-180).
--   Instantiated below at n = 9 against KValue's Fin 14.  Character
--   for character the record's own two fields; nothing is weakened.
-- =====================================================================

record ValPair {n : ℕ} (K : Fin (5 + n)) (γ' : S ^ (11 + n))
  : Type (ℓ-suc ℓ) where
  field
    valK : (k : ℕ) (c ar a b yc : S)
         → ⟨ fst c ∈ fst (lookup (suc (suc zero)) γ') ⟩
         → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
         → ⟨ pr (fst c) (fst yc) ∈ fst (lookup (suc zero) γ') ⟩
         → ⟨ fst yc ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
    valK-un : (k : ℕ) (c ar a yc : S)
            → ⟨ fst c ∈ fst (lookup (suc (suc zero)) γ') ⟩
            → fst c ≡ pr (fst ar) (pr (# k) (fst a))
            → ⟨ pr (fst c) (fst yc) ∈ fst (lookup (suc zero) γ') ⟩
            → ⟨ fst yc ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩

-- =====================================================================
-- THE TERM, at a generic carrier (W2).
--
--   `valSub` is the hypothesis: every member of slot one is a member
--   of K.  It is the WEAKEST of the three candidates section
--   `## WHAT SLOT ONE MUST SATISFY` compares, and it is exactly the
--   shape KFacts already uses for the CARRIER slot
--   (`carrierK`, src/L/Condensation.lagda.md:6113).
--
--   THE CODE PREMISES ARE NOT PARAMETERS HERE.  `valK` takes `c∈` and
--   the shape equation; this term reads neither.  That is why ONE
--   term serves both valK and valK-un: the shape equation is their
--   only difference and it is inert.
--
--   ChainZ (src/L/Condensation.lagda.md:2820-2917) owns the pair
--   pieces and they are public.  Nothing here re-derives them.
-- =====================================================================

module Val {m : ℕ} (K : Fin m) (γ : S ^ m)
  (arityK : (N v : S) → ⟨ fst v ∈ fst N ⟩
          → ⟨ fst N ∈ fst (lookup K γ) ⟩
          → ⟨ fst v ∈ fst (lookup K γ) ⟩) where

  module Z = ChainZ {m} K γ arityK

  -- `SubK E` is the hypothesis, at ANY set E and not only at a slot:
  -- every member of E is a member of K.  It is KFacts's own shape for
  -- the CARRIER (`carrierK`, src/L/Condensation.lagda.md:6113) with
  -- the carrier slot replaced by E.
  SubK : S → Type (ℓ-suc ℓ)
  SubK E = (x : S) → ⟨ fst x ∈ fst E ⟩ → ⟨ fst x ∈ fst (lookup K γ) ⟩

  -- THE TERM.  A Kuratowski pair in E gives up its SECOND component.
  -- Two arityK steps down the pair, after SubK puts the pair in K.
  sndK : (E : S) → SubK E → (c yc : S)
       → ⟨ pr (fst c) (fst yc) ∈ fst E ⟩
       → ⟨ fst yc ∈ fst (lookup K γ) ⟩
  sndK E sub c yc p =
    arityK (pairʟ c yc) yc (Z.y∈pairʟxy c yc)
      (arityK (prʟ c yc) (pairʟ c yc) (Z.ysingl∈prxy c yc)
        (sub (prʟ c yc) (Z.prʟxy∈z E c yc p)))

  -- The single-membership form, E ∈ K, is STRICTLY STRONGER: it gives
  -- SubK in one arityK step and nothing gives it back.  It is the
  -- exact analogue of [LJ-1.500]'s `C∈K` (Probe500.agda:149).
  memberSubK : (E : S) → ⟨ fst E ∈ fst (lookup K γ) ⟩ → SubK E
  memberSubK E h x hx = arityK E x hx h

  -- SubK is REFLEXIVE at K itself, which is what makes the converse
  -- refutable at the frame below (`Weak.subK-is-strictly-weaker`).
  subK-K : SubK (lookup K γ)
  subK-K x hx = hx

-- =====================================================================
-- THE FRAME.  KValue's telescope.
--
--   [LJ-1.500] measured that the six-fold shift is DEFINITIONAL on
--   `arityK`, so the field projects straight through and `six` need
--   not be rebuilt (agents/tasks/LJ-1-500/Probe500.agda:334-341, and
--   lj-1.500-report.md:405-408).  AGENTS.md:45 says a measured cure
--   does not transfer by analogy, so `arityK'` below RE-MEASURES it at
--   this site rather than citing it.  66 lines of KFactsCons are not
--   paid twice.
-- =====================================================================

module Frame
  (lam : V ℓ) (ordλ : IsOrd lam)
  (succλ : (d : V ℓ) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ lam ⟩)
  (gam : V ℓ) (ordγ : IsOrd gam) (γ∈λ : ⟨ gam ∈ lam ⟩) where

  open KValue lam ordλ succλ ∅∈λ gam ordγ γ∈λ

  arityK' : (c1 c2 c3 c4 c5 c6 : S)
    → KFacts iA iK i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 Kenv
    → (N v : S) → ⟨ fst v ∈ fst N ⟩
    → ⟨ fst N ∈ fst (lookup (suc (suc (suc (suc (suc (suc iK))))))
                       (c6 ∷ c5 ∷ c4 ∷ c3 ∷ c2 ∷ c1 ∷ Kenv)) ⟩
    → ⟨ fst v ∈ fst (lookup (suc (suc (suc (suc (suc (suc iK))))))
                       (c6 ∷ c5 ∷ c4 ∷ c3 ∷ c2 ∷ c1 ∷ Kenv)) ⟩
  arityK' c1 c2 c3 c4 c5 c6 f = f .arityK

  module At (c1 c2 c3 c4 c5 c6 : S)
    (f : KFacts iA iK i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 Kenv)
    (valSub : (x : S)
            → ⟨ fst x ∈ fst (lookup (suc zero)
                              (c6 ∷ c5 ∷ c4 ∷ c3 ∷ c2 ∷ c1 ∷ Kenv)) ⟩
            → ⟨ fst x ∈ fst (lookup (suc (suc (suc (suc (suc (suc iK))))))
                              (c6 ∷ c5 ∷ c4 ∷ c3 ∷ c2 ∷ c1 ∷ Kenv)) ⟩)
    where

    γ' : S ^ 20
    γ' = c6 ∷ c5 ∷ c4 ∷ c3 ∷ c2 ∷ c1 ∷ Kenv

    module R = Val {20} (suc (suc (suc (suc (suc (suc iK))))))
                 γ' (arityK' c1 c2 c3 c4 c5 c6 f)

    -- THE OBLIGATION.  Both fields, one term: `valK-un` differs from
    -- `valK` only in the shape equation, which neither reads.
    valK-family : ValPair {n = 9} iK γ'
    valK-family = record
      { valK    = λ k c ar a b yc c∈ shEq p →
                    R.sndK (lookup (suc zero) γ') valSub c yc p
      ; valK-un = λ k c ar a yc c∈ shEq p →
                    R.sndK (lookup (suc zero) γ') valSub c yc p }

  -- WHICH HYPOTHESIS IS WEAKER IS MEASURED, NOT ARGUED.  `memberSubK`
  -- turns E ∈ K into SubK E in one arityK.  The converse is FALSE at
  -- this frame: at E the bound itself, SubK holds by identity and
  -- E ∈ K is refuted by ∈-irrefl.  So SubK is STRICTLY weaker and it
  -- is the hypothesis the obligation takes.
  module Weak (c1 c2 c3 c4 c5 c6 : S)
    (f : KFacts iA iK i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 Kenv) where

    γ' : S ^ 20
    γ' = c6 ∷ c5 ∷ c4 ∷ c3 ∷ c2 ∷ c1 ∷ Kenv

    module R = Val {20} (suc (suc (suc (suc (suc (suc iK))))))
                 γ' (arityK' c1 c2 c3 c4 c5 c6 f)

    subK-is-strictly-weaker :
        ( (E : S) → R.SubK E
        → ⟨ fst E ∈ fst (lookup (suc (suc (suc (suc (suc (suc iK)))))) γ') ⟩ )
      → Empty.⊥
    subK-is-strictly-weaker g =
      ∈-irrefl (fst (lookup (suc (suc (suc (suc (suc (suc iK)))))) γ'))
        (g (lookup (suc (suc (suc (suc (suc (suc iK)))))) γ') R.subK-K)

  -- SIDE-FINDING, and NOT the obligation's hypothesis.  It pins
  -- nothing: it is a CONDITIONAL, offered to [LJ-1.505], which owns
  -- the question of what occupies each front slot.  IF slot one turns
  -- out to be the carrier slot, `carrierK` supplies `valSub` with no
  -- new frame entry at all.  `carrierK` is about `lookup (suc⁶ iA)`,
  -- which is position 6 of γ', and slot one is position 1, so the two
  -- are different slots until something says otherwise.
  valSub-from-carrier : (c1 c2 c3 c4 c5 c6 : S)
    → KFacts iA iK i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 Kenv
    → fst (lookup (suc zero) (c6 ∷ c5 ∷ c4 ∷ c3 ∷ c2 ∷ c1 ∷ Kenv))
       ≡ fst (lookup (suc (suc (suc (suc (suc (suc iA))))))
               (c6 ∷ c5 ∷ c4 ∷ c3 ∷ c2 ∷ c1 ∷ Kenv))
    → (x : S)
    → ⟨ fst x ∈ fst (lookup (suc zero)
                      (c6 ∷ c5 ∷ c4 ∷ c3 ∷ c2 ∷ c1 ∷ Kenv)) ⟩
    → ⟨ fst x ∈ fst (lookup (suc (suc (suc (suc (suc (suc iK))))))
                      (c6 ∷ c5 ∷ c4 ∷ c3 ∷ c2 ∷ c1 ∷ Kenv)) ⟩
  valSub-from-carrier c1 c2 c3 c4 c5 c6 f q x hx =
    f .carrierK x (subst (λ u → ⟨ fst x ∈ u ⟩) q hx)

  -- ===================================================================
  -- THE HYPOTHESIS IS NECESSARY, AND THIS MEASURES IT.
  --
  --   The bare field at THIS frame, with the full KFacts value
  --   supplied, is false.  The counterexample is deliberately kind to
  --   the code half: the code is a well formed four-part code whose
  --   arity IS the numeral 0, so [LJ-1.506]'s refutation is not being
  --   re-run here and nothing turns on junk in slot two.  Slot one is
  --   the successor of ONE pair, and that pair's second component is
  --   the bound itself, which cannot be a member of itself.
  -- ===================================================================

  inner2 innerCode goodCode : S
  inner2 = prʟ (numeralL 0) (numeralL 0)
  innerCode = prʟ (numeralL 0) inner2
  goodCode = prʟ (numeralL 0) innerCode

  -- yc: the bound itself.  fst (lookup (suc⁶ iK) γ') reduces to this.
  badVal : S
  badVal = LsetS lam ordλ

  codeSlot valSlot : S
  codeSlot = sucʟ goodCode
  valSlot = sucʟ (prʟ goodCode badVal)

  code∈ : ⟨ fst goodCode ∈ fst codeSlot ⟩
  code∈ = subst (λ u → ⟨ fst goodCode ∈ u ⟩) (sym (sucʟ-fst goodCode))
            (self∈sucV (fst goodCode))

  good-shape : fst goodCode
             ≡ pr (fst (numeralL 0))
                 (pr (# 0) (pr (fst (numeralL 0)) (fst (numeralL 0))))
  good-shape =
      prʟ-fst (numeralL 0) innerCode
    ∙ cong (pr (fst (numeralL 0)))
        ( prʟ-fst (numeralL 0) inner2
        ∙ cong₂ pr (numeralL-fst 0) (prʟ-fst (numeralL 0) (numeralL 0)) )

  pair∈ : ⟨ pr (fst goodCode) (fst badVal) ∈ fst valSlot ⟩
  pair∈ =
    subst (λ u → ⟨ pr (fst goodCode) (fst badVal) ∈ u ⟩)
      (sym (sucʟ-fst (prʟ goodCode badVal)))
      (subst (λ w → ⟨ w ∈ sucV (fst (prʟ goodCode badVal)) ⟩)
        (prʟ-fst goodCode badVal)
        (self∈sucV (fst (prʟ goodCode badVal))))

  -- The bare field: no hypothesis about slot one anywhere.
  BareValK : Type (ℓ-suc ℓ)
  BareValK = (c1 c2 c3 c4 c5 c6 : S)
           → KFacts iA iK i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 Kenv
           → (k : ℕ) (c ar a b yc : S)
           → ⟨ fst c ∈ fst (lookup (suc (suc zero))
                             (c6 ∷ c5 ∷ c4 ∷ c3 ∷ c2 ∷ c1 ∷ Kenv)) ⟩
           → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
           → ⟨ pr (fst c) (fst yc) ∈ fst (lookup (suc zero)
                             (c6 ∷ c5 ∷ c4 ∷ c3 ∷ c2 ∷ c1 ∷ Kenv)) ⟩
           → ⟨ fst yc ∈ fst (lookup (suc (suc (suc (suc (suc (suc iK))))))
                             (c6 ∷ c5 ∷ c4 ∷ c3 ∷ c2 ∷ c1 ∷ Kenv)) ⟩

  valK-bare-is-false : BareValK → Empty.⊥
  valK-bare-is-false h =
    ∈-irrefl (fst badVal)
      (h (numeralL 0) (numeralL 0) (numeralL 0) codeSlot valSlot
         (numeralL 0) facts 0 goodCode (numeralL 0) (numeralL 0)
         (numeralL 0) badVal code∈ good-shape pair∈)

valK-family = Frame.At.valK-family

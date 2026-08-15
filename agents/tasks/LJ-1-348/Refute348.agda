{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.348] THE PROBE.  IS `witK` TRUE AS STATED?
--
-- D-10: price the TRUTH of a recorded residue before pricing its proof.
--
-- `[LJ-1.344]` reported: 「`witK` HAS THE SAME SHAPE DEFECT AS THE TWO
-- REFUTED TIES ... It is NOT refutable by [LJ-1.341]'s countermodel,
-- MEASURED, because `shapedAt` blocks it」, and priced the cure at ONE
-- `carrierK` call.  This file tests the first half.
--
-- THE TIE, verbatim from src/L/Condensation.lagda.md:6683-6685
-- (`WitnessAgree`) and :7233-7235 (`LeafAgree`):
--
--   (witK : (w : S) -> < (w : g) |= ((var (suc x) in var zero)
--                /\ (closedAt zero /\ shapedAt zero (suc A))) >
--          -> < fst w in fst (lookup K g) >)
--
-- WHY `shapedAt` DOES NOT BLOCK IT.  `shapes` (src/L/Coding/Shape.lagda.md:182-187)
-- is a twelve-fold disjunction, and the tag-6 disjunct is
-- `unForm 6 zeroPay`.  `unForm` (:104-105) is
--   `E (E (arityTagAtL (suc (suc zero)) (suc zero) k zero /\ rel))`,
-- so a tag-6 member of `w` is `pr (fst N) (pr (# 6) (fst a))` where
-- `zeroPay` (:178) pins `a` to the numeral ZERO and NOTHING pins `N`.
-- The ARITY component of a shape is FREE.
--
-- WHY `closedAt` DOES NOT BLOCK IT EITHER.  `closedAt`
-- (src/L/Coding/Model.lagda.md:2191-2195) is eight clauses at tags
-- 2, 3, 4, 5, 8, 9, 10 and 11.  TAG 6 IS IN NONE OF THEM.  So every
-- clause is vacuous on a set whose only member carries tag 6.
--
-- THE COUNTERMODEL.  Put the BOUND ITSELF in the free arity slot:
--   c  := prl B (prl (numeral 6) (numeral 0)),  B := lookup K g
--   w' := pairl c c,  the L-side singleton of that one shape.
-- `w'` is shaped, `w'` is closed, and the conclusion `fst w' in b`
-- closes a FOUR-step membership cycle, which `regularityV`
-- (src/V/Hierarchy.lagda.md:139-144) refutes.
--
-- The refutation needs ONE thing of the environment: the slot `x` the
-- premise reads must hold that same shape.  That slot is a free
-- parameter of `WitnessAgree` and of `LeafAgree`, so the module below
-- takes the equation as a hypothesis and PART 2 inhabits it.
--
-- ONE agda process under GHCRTS="-A64m -I0 -M8g".

open import Base.Prelude
open import Base.Truth

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _∈̇_; _∧̇_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆; ⁅_⁆s; pairing-ax ) renaming ( module InfinitySet to Inf )
open Inf using ( #_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ∈∈ₛ )
open import Cubical.Induction.WellFounded using ( Acc; acc )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Unit using ( Unit; tt )
open import Cubical.Data.Nat using ( _+_ )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )

module LJ-1-348.Refute348 {ℓ : Level} where

open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; regularityV; ∈-irrefl )
open import V.Coding {ℓ} using ( pr; pr-inj; #-inj )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.Axioms.Numerals {ℓ}
  using ( numeralL; numeralL-fst; pairʟ; pairʟ-fst )

import L.Coding.Model
module GM = L.Coding.Model {ℓ}
open GM using ( prʟ; prʟ-fst; closedAt; binShape-in; unShape-in )
open GM.AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

open import L.Coding.Shape {ℓ}
  using ( shapedAt; shaped-in; ShapeWit; UnWit; zeroPay )

open hPropStructure 𝒮ʟ using ( S )
module HV = hPropStructure 𝒮ᵥ

-- =====================================================================
-- PART 0.  MEMBERSHIP CYCLES AND PAIR ACCESS.
--
-- `noCycle4` is `[LJ-1.341]`'s own, at
-- agents/tasks/LJ-1-341/ProbeTies341.agda:94-96, an accessibility
-- recursion on `regularityV`.  The three pair memberships are the same
-- three `[LJ-1.302]` wrote; `[LJ-1.346]` ruled that the chapter's
-- `ChainZ.pair∈pr` is the public home, but `ChainZ` takes an `arityK`
-- this file has no reason to invent, so they are re-written here.
-- =====================================================================

noCycle4 : (a : V ℓ) → Acc HV._∈ᵗ_ a → (b c d : V ℓ)
         → ⟨ a ∈ b ⟩ → ⟨ b ∈ c ⟩ → ⟨ c ∈ d ⟩ → ⟨ d ∈ a ⟩ → Empty.⊥
noCycle4 a (acc rec) b c d ab bc cd da = noCycle4 d (rec d da) a b c da ab bc cd

x∈pair : (x y : V ℓ) → ⟨ x ∈ ⁅ x , y ⁆ ⟩
x∈pair x y =
  ∈∈ₛ {a = x} {b = ⁅ x , y ⁆} .snd (pairing-ax x y x .snd ∣ inl refl ∣₁)

pair∈pr : (x y : V ℓ) → ⟨ ⁅ x , y ⁆ ∈ pr x y ⟩
pair∈pr x y =
  ∈∈ₛ {a = ⁅ x , y ⁆} {b = pr x y} .snd
    (pairing-ax ⁅ x ⁆s ⁅ x , y ⁆ ⁅ x , y ⁆ .snd ∣ inr refl ∣₁)

pair-only : (x d : V ℓ) → ⟨ d ∈ ⁅ x , x ⁆ ⟩ → d ≡ x
pair-only x d h = PT.rec (setIsSet d x) (λ { (inl p) → p ; (inr p) → p })
  (pairing-ax x x d .fst (∈∈ₛ {a = d} {b = ⁅ x , x ⁆} .fst h))

-- Six is not any of the eight tags `closedAt` speaks about.  One family
-- rather than eight lemmas, because every clause needs the same step.
Not6 : ℕ → Type
Not6 6 = Empty.⊥
Not6 _ = Unit

6≢ : (k : ℕ) → Not6 k → 6 ≡ k → Empty.⊥
6≢ k nk p = subst Not6 (sym p) nk

-- =====================================================================
-- PART 1.  THE COUNTERMODEL.
--
-- Generic in the environment, the carrier slot, the bound slot and the
-- read slot, so it covers `WitnessAgree`'s form and `LeafAgree`'s form
-- at once.  PART 3 states both verbatim and discharges them here.
-- =====================================================================

module Refute {n : ℕ} (A Ki xi : Fin n) (γ : S ^ n)
  (hx : fst (lookup xi γ) ≡ pr (fst (lookup Ki γ)) (pr (# 6) (# 0))) where

  B : S
  B = lookup Ki γ

  b : V ℓ
  b = fst B

  -- THE SHAPE.  Tag 6, payload the numeral zero, ARITY THE BOUND.
  -- Built with `prʟ`, the chapter's own pair on the L side, so it is
  -- an element of the carrier and not a bare ambient set.
  c : S
  c = prʟ B (prʟ (numeralL 6) (numeralL 0))

  p60 : V ℓ
  p60 = pr (# 6) (# 0)

  c-fst : fst c ≡ pr b p60
  c-fst = prʟ-fst B (prʟ (numeralL 6) (numeralL 0))
        ∙ cong (λ u → pr b u)
            (prʟ-fst (numeralL 6) (numeralL 0)
             ∙ cong₂ pr (numeralL-fst 6) (numeralL-fst 0))

  -- THE WITNESS SET.  The L-side singleton of that one shape.
  w' : S
  w' = pairʟ c c

  w'-fst : fst w' ≡ ⁅ fst c , fst c ⁆
  w'-fst = pairʟ-fst c c

  c∈w' : ⟨ fst c ∈ fst w' ⟩
  c∈w' = subst (λ u → ⟨ fst c ∈ u ⟩) (sym w'-fst) (x∈pair (fst c) (fst c))

  only-c : (e : S) → ⟨ fst e ∈ fst w' ⟩ → fst e ≡ fst c
  only-c e h = pair-only (fst c) (fst e)
                 (subst (λ u → ⟨ fst e ∈ u ⟩) w'-fst h)

  -- Every member of `w'` carries tag 6, so a clause about tag `k` fires
  -- on nothing unless `k` is 6.
  tagIs : (e ar : S) (k : ℕ) (rest : V ℓ)
        → ⟨ fst e ∈ fst w' ⟩
        → fst e ≡ pr (fst ar) (pr (# k) rest)
        → 6 ≡ k
  tagIs e ar k rest he q =
    #-inj 6 k (pr-inj (pr-inj (sym (only-c e he ∙ c-fst) ∙ q) .snd) .fst)

  clash : (k : ℕ) → Not6 k → (e ar : S) (rest : V ℓ)
        → ⟨ fst e ∈ fst w' ⟩ → fst e ≡ pr (fst ar) (pr (# k) rest)
        → Empty.⊥
  clash k nk e ar rest he q = 6≢ k nk (tagIs e ar k rest he q)

  -- CLOSEDNESS, and it is vacuous.  Eight clauses, tags 2, 3, 4, 5, 8,
  -- 9, 10 and 11.  Each one is refused at its own tag.
  private
    binVac : (k : ℕ) → Not6 k
           → ⟨ (w' ∷ γ) ⊨ GM.binShapeAt zero k (GM.bothSameAt zero) ⟩
    binVac k nk = binShape-in zero k (GM.bothSameAt zero) (w' ∷ γ)
      (λ e ar a bb he q →
        Empty.rec (clash k nk e ar (pr (fst a) (fst bb)) he q))

    binVac' : (k : ℕ) → Not6 k
            → ⟨ (w' ∷ γ) ⊨ GM.binShapeAt zero k (GM.succSndAt zero) ⟩
    binVac' k nk = binShape-in zero k (GM.succSndAt zero) (w' ∷ γ)
      (λ e ar a bb he q →
        Empty.rec (clash k nk e ar (pr (fst a) (fst bb)) he q))

    unVac : (k : ℕ) → Not6 k
          → ⟨ (w' ∷ γ) ⊨ GM.unShapeAt zero k (GM.oneSameAt zero) ⟩
    unVac k nk = unShape-in zero k (GM.oneSameAt zero) (w' ∷ γ)
      (λ e ar a he q → Empty.rec (clash k nk e ar (fst a) he q))

    unVac' : (k : ℕ) → Not6 k
           → ⟨ (w' ∷ γ) ⊨ GM.unShapeAt zero k (GM.oneSuccAt zero) ⟩
    unVac' k nk = unShape-in zero k (GM.oneSuccAt zero) (w' ∷ γ)
      (λ e ar a he q → Empty.rec (clash k nk e ar (fst a) he q))

  closed : ⟨ (w' ∷ γ) ⊨ closedAt zero ⟩
  closed = binVac 2 tt
         , ( binVac 3 tt
           , ( binVac 4 tt
             , ( unVac 5 tt
               , ( unVac' 8 tt
                 , ( unVac' 9 tt
                   , ( binVac' 10 tt , binVac' 11 tt ) ) ) ) ) )

  -- SHAPEDNESS, and it holds at the SIXTH disjunct.  Nothing about the
  -- carrier `A` is used, which is the point: tag 6 names no carrier
  -- member, so the shape predicate cannot bound the arity slot.
  shaped : ⟨ (w' ∷ γ) ⊨ shapedAt zero (suc A) ⟩
  shaped = shaped-in zero (suc A) (w' ∷ γ) g
    where
    wit : (e : S) → ⟨ fst e ∈ fst w' ⟩ → UnWit 6 zeroPay (w' ∷ γ) e
    wit e he = B , ( numeralL 0
                   , ( only-c e he ∙ c-fst
                       ∙ cong (λ u → pr b (pr (# 6) u)) (sym (numeralL-fst 0))
                     , refl ) )

    g : (e : S) → ⟨ fst e ∈ fst w' ⟩ → PT.∥ ShapeWit (suc A) (w' ∷ γ) e ∥₁
    g e he = ∣ inr (inr (inr (inr (inr (inr (inl (wit e he))))))) ∣₁

  -- THE PREMISE, INHABITED.  This is the non-vacuity control: a
  -- hypothesis can look refutable because nothing meets its premise.
  -- All three conjuncts are terms.
  x∈w' : ⟨ fst (lookup xi γ) ∈ fst w' ⟩
  x∈w' = subst (λ u → ⟨ u ∈ fst w' ⟩) (sym (hx ∙ sym c-fst)) c∈w'

  premise : ⟨ (w' ∷ γ) ⊨ ((var (suc xi) ∈̇ var zero)
              ∧̇ (closedAt zero ∧̇ shapedAt zero (suc A))) ⟩
  premise = x∈w' , ( closed , shaped )

  -- THE TIE, at the generic index form.
  WitK : Type (ℓ-suc ℓ)
  WitK = (u : S) → ⟨ (u ∷ γ) ⊨ ((var (suc xi) ∈̇ var zero)
              ∧̇ (closedAt zero ∧̇ shapedAt zero (suc A))) ⟩
       → ⟨ fst u ∈ fst (lookup Ki γ) ⟩

  -- THE REFUTATION.  Four steps down:
  --   b in {b, pr 6 0} in c in {c, c} in b.
  witK-false : WitK → Empty.⊥
  witK-false h =
    noCycle4 b (regularityV b) ⁅ b , p60 ⁆ (fst c) (fst w')
      (x∈pair b p60)
      (subst (λ u → ⟨ ⁅ b , p60 ⁆ ∈ u ⟩) (sym c-fst) (pair∈pr b p60))
      c∈w'
      (h w' premise)

  -- CONTROL.  The bound is not made empty by any of this; the one thing
  -- the hierarchy refuses is the cycle itself.
  self-blocked : ⟨ b ∈ b ⟩ → Empty.⊥
  self-blocked = ∈-irrefl b

-- =====================================================================
-- PART 2.  NON-VACUITY OF THE HYPOTHESIS `hx`.
--
-- The refutation asks the read slot to hold the shape.  That slot is a
-- free parameter at both sites, so the demand is met by an environment
-- and not by an assumption.  Two slots suffice.
-- =====================================================================

module Live (Bset : S) where

  shapeOf : S
  shapeOf = prʟ Bset (prʟ (numeralL 6) (numeralL 0))

  env2 : S ^ 2
  env2 = shapeOf ∷ Bset ∷ []

  -- slot 0 is the read slot, slot 1 is the bound; the carrier slot is
  -- the bound as well, which the refutation never looks at.
  hx-live : fst (lookup zero env2)
          ≡ pr (fst (lookup (suc zero) env2)) (pr (# 6) (# 0))
  hx-live = prʟ-fst Bset (prʟ (numeralL 6) (numeralL 0))
          ∙ cong (λ u → pr (fst Bset) u)
              (prʟ-fst (numeralL 6) (numeralL 0)
               ∙ cong₂ pr (numeralL-fst 6) (numeralL-fst 0))

  module R = Refute {2} (suc zero) (suc zero) zero env2 hx-live

  -- The tie is EMPTY at this environment, and the environment is built
  -- from one arbitrary carrier element.
  empty-here : R.WitK → Empty.⊥
  empty-here = R.witK-false

-- =====================================================================
-- PART 3.  THE CHAPTER'S OWN TWO INDEX FORMS, VERBATIM.
--
-- `WitnessAgree` (src/L/Condensation.lagda.md:6683-6685) and
-- `LeafAgree` (:7233-7235).  Both are instances of `Refute.WitK`, and
-- both are discharged into the empty type.
-- =====================================================================

module ChapterForms {n : ℕ} where

  -- `WitnessAgree`'s form, at its own binder names.
  WitnessForm : (A x K : Fin n) (γ : S ^ n) → Type (ℓ-suc ℓ)
  WitnessForm A x K γ =
    (w : S) → ⟨ (w ∷ γ) ⊨ ((var (suc x) ∈̇ var zero)
                 ∧̇ (closedAt zero ∧̇ shapedAt zero (suc A))) ⟩
    → ⟨ fst w ∈ fst (lookup K γ) ⟩

  witness-false : (A x K : Fin n) (γ : S ^ n)
    → fst (lookup x γ) ≡ pr (fst (lookup K γ)) (pr (# 6) (# 0))
    → WitnessForm A x K γ → Empty.⊥
  witness-false A x K γ hx = Refute.witK-false A K x γ hx

  -- `LeafAgree`'s form, at its own five-plus-three index shape.
  LeafForm : (w K : Fin (5 + n)) (γ : S ^ (8 + n)) → Type (ℓ-suc ℓ)
  LeafForm w K γ =
    (w' : S) → ⟨ (w' ∷ γ) ⊨ ((var (suc (suc zero)) ∈̇ var zero)
                 ∧̇ (closedAt zero ∧̇ shapedAt zero (suc (suc (suc (suc w)))))) ⟩
    → ⟨ fst w' ∈ fst (lookup (suc (suc (suc K))) γ) ⟩

  leaf-false : (w K : Fin (5 + n)) (γ : S ^ (8 + n))
    → fst (lookup (suc zero) γ)
      ≡ pr (fst (lookup (suc (suc (suc K))) γ)) (pr (# 6) (# 0))
    → LeafForm w K γ → Empty.⊥
  leaf-false w K γ hx =
    Refute.witK-false (suc (suc (suc w))) (suc (suc (suc K))) (suc zero) γ hx

-- =====================================================================
-- PART 4.  CONTROL 3, AFTER `[LJ-1.341]`.  THE CURE IS A TERM, AND THE
-- REFUTATION IS ABOUT THE QUANTIFIER AND NOT ABOUT THE FORMULA.
--
-- `[LJ-1.344]` priced the cure at ONE `carrierK` call.  It IS one call,
-- and the type it proves is not the type the chapter needs: the extra
-- hypothesis is the carrier membership of `w` itself, and PART 5 of the
-- report measures that no call site holds it.
-- =====================================================================

module Cure {n : ℕ} (A Ki xi : Fin n) (γ : S ^ n)
  (carrierK : (v : S) → ⟨ fst v ∈ fst (lookup A γ) ⟩
            → ⟨ fst v ∈ fst (lookup Ki γ) ⟩) where

  witK-bounded : (u : S) → ⟨ fst u ∈ fst (lookup A γ) ⟩
               → ⟨ (u ∷ γ) ⊨ ((var (suc xi) ∈̇ var zero)
                    ∧̇ (closedAt zero ∧̇ shapedAt zero (suc A))) ⟩
               → ⟨ fst u ∈ fst (lookup Ki γ) ⟩
  witK-bounded u hu _ = carrierK u hu

{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.341] THE PROBE.  ARE `envK` AND `defPairK` TRUE AS STATED?
--
-- D-10: price the TRUTH of a recorded residue before pricing its proof.
--
-- `[LJ-1.338]` measured `LeafAgree`'s ambient tie supply at 327 lines and
-- flagged 51 of them as a residue nothing proves.  It marked two of the
-- ties INFERRED-may-be-false, and it built no counterexample.  This file
-- builds one.
--
-- THE TWO TIES, verbatim from src/L/Condensation.lagda.md:7183-7186:
--
--   (envK : (E z : S) -> < (E : z : g) |= envOneAt zero (suc zero) >
--          -> < fst E in fst (lookup (suc (suc (suc K))) g) >)
--   (defPairK : (E z w' : S)
--          -> < (w' : E : z : g) |= tagAtL zero 0 (suc (suc zero)) >
--          -> < fst w' in fst (lookup (suc (suc (suc K))) g) >)
--
-- The same two are module parameters of `DefinesAgree` at
-- src/L/Condensation.lagda.md:6779-6785, and `LeafAgree` hands them
-- straight through at :7205-7206.
--
-- WHAT THE TWO FORMULAS SAY.  The brief asked for this reading first.
--   * `tagAtL-adequate` (src/L/Coding/Model.lagda.md:588-590) makes
--     `tagAtL s k x` at an environment EQUAL to the bare set equation
--     `fst (lookup s g) = pr (# k) (fst (lookup x g))`.  It holds no
--     membership, so it bounds nothing.
--   * `envOneAt` (src/L/Coding/Powerset.lagda.md:128-129) is `extAt`
--     applied to that same tag reader, and `envOneAt-out` (:157) makes it
--     EQUAL to `fst E = envOne (fst z)`.  Again a bare equation.
-- So the satisfaction premise does NOT bound `z`.  MEASURED, by reading
-- the definitions and by the two terms below.
--
-- THE COUNTERMODEL.  Instantiate `z` with the BOUND ITSELF, the set the
-- conclusion names.  Then the conclusion asserts a membership cycle, and
-- `regularityV` (src/V/Hierarchy.lagda.md:139-144) refutes it.  The
-- refutation holds for EVERY environment and EVERY slot index, so the
-- two hypotheses are UNINHABITED types, not merely unproved ones.
--
-- INDEX ABSTRACTION.  The chapter writes `lookup (suc (suc (suc K))) g`.
-- That is one instance of `lookup Ki g` for `Ki : Fin n`, so the module
-- below quantifies over `Ki` and covers the chapter's site exactly.
--
-- ONE agda process under GHCRTS="-A64m -I0 -M8g".

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

open import FOL.ZFStructure using ( module hPropStructure )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆; ⁅_⁆s; pairing-ax ) renaming ( module InfinitySet to Inf )
open Inf using ( #_ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ∈∈ₛ; extensionality; _⊆_ )
open import Cubical.Induction.WellFounded using ( Acc; acc )
open import Cubical.Data.Sum using ( inl; inr )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )

module LJ-1-341.ProbeTies341 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; regularityV; ∈-irrefl )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.Axioms.Numerals {ℓ}
  using ( numeralL; numeralL-fst; pairʟ; pairʟ-fst )

import L.Coding.Model
module GM = L.Coding.Model {ℓ}
open GM using ( tagAtL; tagAtL-adequate; prʟ; prʟ-fst; extAt-in-both )
open GM.AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

open import L.Coding.Powerset {ℓ} lem using ( envOneAt; envOne; envOneAt-out )

open hPropStructure 𝒮ʟ using ( S )
module HV = hPropStructure 𝒮ᵥ

-- =====================================================================
-- PART 0.  MEMBERSHIP CYCLES.  Two lines each, from the hierarchy's own
-- regularity.  Nothing here is new mathematics; `∈-irrefl`
-- (src/V/Hierarchy.lagda.md:155-156) is the length-one case and the
-- chapter already uses it.
-- =====================================================================

noCycle3 : (a : V ℓ) → Acc HV._∈ᵗ_ a → (b c : V ℓ)
         → ⟨ a ∈ b ⟩ → ⟨ b ∈ c ⟩ → ⟨ c ∈ a ⟩ → Empty.⊥
noCycle3 a (acc rec) b c ab bc ca = noCycle3 c (rec c ca) a b ca ab bc

noCycle4 : (a : V ℓ) → Acc HV._∈ᵗ_ a → (b c d : V ℓ)
         → ⟨ a ∈ b ⟩ → ⟨ b ∈ c ⟩ → ⟨ c ∈ d ⟩ → ⟨ d ∈ a ⟩ → Empty.⊥
noCycle4 a (acc rec) b c d ab bc cd da = noCycle4 d (rec d da) a b c da ab bc cd

-- The three pair memberships.  These are the SAME three lines
-- `[LJ-1.302]` wrote at agents/tasks/LJ-1-302/ProbeLJ1302B.agda:97-108,
-- copied because importing that probe would pull its whole ambient
-- frame in.
x∈pair : (x y : V ℓ) → ⟨ x ∈ ⁅ x , y ⁆ ⟩
x∈pair x y =
  ∈∈ₛ {a = x} {b = ⁅ x , y ⁆} .snd (pairing-ax x y x .snd ∣ inl refl ∣₁)

y∈pair : (x y : V ℓ) → ⟨ y ∈ ⁅ x , y ⁆ ⟩
y∈pair x y =
  ∈∈ₛ {a = y} {b = ⁅ x , y ⁆} .snd (pairing-ax x y y .snd ∣ inr refl ∣₁)

pair∈pr : (x y : V ℓ) → ⟨ ⁅ x , y ⁆ ∈ pr x y ⟩
pair∈pr x y =
  ∈∈ₛ {a = ⁅ x , y ⁆} {b = pr x y} .snd
    (pairing-ax ⁅ x ⁆s ⁅ x , y ⁆ ⁅ x , y ⁆ .snd ∣ inr refl ∣₁)

pair-only : (x d : V ℓ) → ⟨ d ∈ ⁅ x , x ⁆ ⟩ → d ≡ x
pair-only x d h = PT.rec (setIsSet d x) (λ { (inl p) → p ; (inr p) → p })
  (pairing-ax x x d .fst (∈∈ₛ {a = d} {b = ⁅ x , x ⁆} .fst h))

-- The one-entry environment IS the singleton of its only entry.  The two
-- clauses are `[LJ-1.336]`'s own two, at
-- src/L/Coding/Powerset.lagda.md:137-142, read at the hierarchy instead
-- of at the model.
module _ (v : V ℓ) where
  private
    a₀ : V ℓ
    a₀ = pr (# 0) v

    readEntry : (w : V ℓ) → ⟨ w ∈ envOne v ⟩ → w ≡ a₀
    readEntry w = PT.rec (setIsSet w a₀)
      (λ { (lift zero , q) → sym q ; (lift (suc ()) , _) })

    entry∈ : (w : V ℓ) → w ≡ a₀ → ⟨ w ∈ envOne v ⟩
    entry∈ w q = ∣ lift zero , sym q ∣₁

  envOne-pair : envOne v ≡ ⁅ a₀ , a₀ ⁆
  envOne-pair = extensionality (envOne v) ⁅ a₀ , a₀ ⁆ (s1 , s2)
    where
    s1 : ⟨ envOne v ⊆ ⁅ a₀ , a₀ ⁆ ⟩
    s1 x x∈ₛ = ∈∈ₛ {a = x} {b = ⁅ a₀ , a₀ ⁆} .fst
      (subst (λ u → ⟨ u ∈ ⁅ a₀ , a₀ ⁆ ⟩)
        (sym (readEntry x (∈∈ₛ {a = x} {b = envOne v} .snd x∈ₛ)))
        (x∈pair a₀ a₀))

    s2 : ⟨ ⁅ a₀ , a₀ ⁆ ⊆ envOne v ⟩
    s2 x x∈ₛ = ∈∈ₛ {a = x} {b = envOne v} .fst
      (entry∈ x (pair-only a₀ x (∈∈ₛ {a = x} {b = ⁅ a₀ , a₀ ⁆} .snd x∈ₛ)))

-- =====================================================================
-- PART 1.  THE COUNTERMODEL.
-- =====================================================================

module Refute {n : ℕ} (Ki : Fin n) (γ : S ^ n) where

  -- The bound.  The set at the slot the two conclusions name.
  B : S
  B = lookup Ki γ

  b : V ℓ
  b = fst B

  -- The tagged pair over the bound itself.  `prʟ` is the chapter's own
  -- pair on the L side, so this IS an element of the carrier.
  W : S
  W = prʟ (numeralL 0) B

  W-fst : fst W ≡ pr (# 0) b
  W-fst = prʟ-fst (numeralL 0) B ∙ cong (λ u → pr u b) (numeralL-fst 0)

  -- ---------------------------------------------------------------
  -- `defPairK`.  Type VERBATIM from src/L/Condensation.lagda.md:7185.
  -- ---------------------------------------------------------------
  DefPairK : Type (ℓ-suc ℓ)
  DefPairK = (E z w' : S)
           → ⟨ (w' ∷ E ∷ z ∷ γ) ⊨ tagAtL zero 0 (suc (suc zero)) ⟩
           → ⟨ fst w' ∈ fst (lookup Ki γ) ⟩

  -- NON-VACUITY, CONTROL 1.  The premise IS inhabited at the witnesses
  -- the refutation uses.  Without this line the hypothesis could be
  -- refuted for the wrong reason, and `[LJ-1.338]`'s third control
  -- tested exactly this failure.
  defPair-premise : ⟨ (W ∷ B ∷ B ∷ γ) ⊨ tagAtL zero 0 (suc (suc zero)) ⟩
  defPair-premise = subst ⟨_⟩
    (sym (tagAtL-adequate zero 0 (suc (suc zero)) (W ∷ B ∷ B ∷ γ))) W-fst

  -- THE REFUTATION.  Three steps down: b in {0,b} in pr 0 b in b.
  defPairK-false : DefPairK → Empty.⊥
  defPairK-false h =
    noCycle3 b (regularityV b) ⁅ # 0 , b ⁆ (pr (# 0) b)
      (y∈pair (# 0) b)
      (pair∈pr (# 0) b)
      (subst (λ u → ⟨ u ∈ b ⟩) W-fst (h B B W defPair-premise))

  -- ---------------------------------------------------------------
  -- `envK`.  Type VERBATIM from src/L/Condensation.lagda.md:7183.
  -- ---------------------------------------------------------------
  Esing : S
  Esing = pairʟ W W

  E-fst : fst Esing ≡ ⁅ fst W , fst W ⁆
  E-fst = pairʟ-fst W W

  EnvK : Type (ℓ-suc ℓ)
  EnvK = (E z : S) → ⟨ (E ∷ z ∷ γ) ⊨ envOneAt zero (suc zero) ⟩
       → ⟨ fst E ∈ fst (lookup Ki γ) ⟩

  -- NON-VACUITY, CONTROL 2.  The one-entry environment over the bound is
  -- an element of the carrier and it satisfies the reader.  Built
  -- through `extAt-in-both`, so nothing about `envOne` is assumed.
  envK-premise : ⟨ (Esing ∷ B ∷ γ) ⊨ envOneAt zero (suc zero) ⟩
  envK-premise =
    extAt-in-both zero (tagAtL zero 0 (suc (suc zero))) (Esing ∷ B ∷ γ) fwd bwd
    where
    fwd : (t : S) → ⟨ fst t ∈ fst (lookup zero (Esing ∷ B ∷ γ)) ⟩
        → ⟨ (t ∷ Esing ∷ B ∷ γ) ⊨ tagAtL zero 0 (suc (suc zero)) ⟩
    fwd t ht = subst ⟨_⟩
      (sym (tagAtL-adequate zero 0 (suc (suc zero)) (t ∷ Esing ∷ B ∷ γ)))
      (pair-only (fst W) (fst t)
        (subst (λ u → ⟨ fst t ∈ u ⟩) E-fst ht) ∙ W-fst)

    bwd : (t : S) → ⟨ (t ∷ Esing ∷ B ∷ γ) ⊨ tagAtL zero 0 (suc (suc zero)) ⟩
        → ⟨ fst t ∈ fst (lookup zero (Esing ∷ B ∷ γ)) ⟩
    bwd t h = subst (λ u → ⟨ fst t ∈ u ⟩) (sym E-fst)
      (subst (λ u → ⟨ u ∈ ⁅ fst W , fst W ⁆ ⟩) (sym eq)
        (x∈pair (fst W) (fst W)))
      where
      eq : fst t ≡ fst W
      eq = subst ⟨_⟩
             (tagAtL-adequate zero 0 (suc (suc zero)) (t ∷ Esing ∷ B ∷ γ)) h
         ∙ sym W-fst

  -- THE REFUTATION.  Four steps down, the same cycle one link longer.
  envK-false : EnvK → Empty.⊥
  envK-false h =
    noCycle4 b (regularityV b) ⁅ # 0 , b ⁆ (pr (# 0) b) ⁅ fst W , fst W ⁆
      (y∈pair (# 0) b)
      (pair∈pr (# 0) b)
      (subst (λ u → ⟨ u ∈ ⁅ fst W , fst W ⁆ ⟩) W-fst (x∈pair (fst W) (fst W)))
      (subst (λ u → ⟨ u ∈ b ⟩) E-fst (h Esing B envK-premise))

  -- =================================================================
  -- CONTROL 3.  THE REPAIR IS NOT EMPTY, AND IT COSTS NOTHING NEW.
  --
  -- Bound `z` by the bound, and `defPairK` becomes a TERM under two
  -- fields the `KFacts` record ALREADY carries: `pairK`
  -- (src/L/Condensation.lagda.md:6107-6108) and `numK0` (:6091).  So
  -- the refutation above is about the QUANTIFIER and not about the tag
  -- formula.
  -- =================================================================
  module Repair
    (pairK : (a c : S) → ⟨ fst a ∈ fst (lookup Ki γ) ⟩
           → ⟨ fst c ∈ fst (lookup Ki γ) ⟩
           → ⟨ fst (prʟ a c) ∈ fst (lookup Ki γ) ⟩)
    (numK0 : ⟨ fst (numeralL 0) ∈ fst (lookup Ki γ) ⟩) where

    defPairK-bounded : (E z w' : S) → ⟨ fst z ∈ fst (lookup Ki γ) ⟩
                     → ⟨ (w' ∷ E ∷ z ∷ γ) ⊨ tagAtL zero 0 (suc (suc zero)) ⟩
                     → ⟨ fst w' ∈ fst (lookup Ki γ) ⟩
    defPairK-bounded E z w' hz h =
      subst (λ u → ⟨ u ∈ b ⟩) (sym eq2) (pairK (numeralL 0) z numK0 hz)
      where
      eq : fst w' ≡ pr (# 0) (fst z)
      eq = subst ⟨_⟩
             (tagAtL-adequate zero 0 (suc (suc zero)) (w' ∷ E ∷ z ∷ γ)) h

      eq2 : fst w' ≡ fst (prʟ (numeralL 0) z)
      eq2 = eq ∙ sym (prʟ-fst (numeralL 0) z
                     ∙ cong (λ u → pr u (fst z)) (numeralL-fst 0))

  -- =================================================================
  -- CONTROL 3b.  THE `envK` REPAIR, AND THE ONE CLOSURE IT ADDS.
  --
  -- `envOneAt-out` (src/L/Coding/Powerset.lagda.md:157) turns the
  -- premise into `fst E = envOne (fst z)`, and `envOne v` is the
  -- SINGLETON of `pr (# 0) v`.  So the repaired `envK` needs a
  -- SINGLETON closure, and `KFacts` (:6079-6112) carries none.
  --
  -- IT IS TWO LINES, NOT A NEW ARCHITECTURE.  `BoundOver` already has
  -- `pr∈λ` (src/L/Coding/Bound.lagda.md:69-70) and `trans∈λ` (:93-94),
  -- and the singleton of `x` is a member of `pr x x`.
  -- =================================================================
  module RepairEnv
    (prIn : (x y : V ℓ) → ⟨ x ∈ b ⟩ → ⟨ y ∈ b ⟩ → ⟨ pr x y ∈ b ⟩)
    (transIn : (x y : V ℓ) → ⟨ y ∈ x ⟩ → ⟨ x ∈ b ⟩ → ⟨ y ∈ b ⟩)
    (numIn : ⟨ # 0 ∈ b ⟩) where

    sgltIn : (x : V ℓ) → ⟨ x ∈ b ⟩ → ⟨ ⁅ x , x ⁆ ∈ b ⟩
    sgltIn x hx = transIn (pr x x) ⁅ x , x ⁆ (pair∈pr x x) (prIn x x hx hx)

    envK-bounded : (E z : S) → ⟨ fst z ∈ b ⟩
                 → ⟨ (E ∷ z ∷ γ) ⊨ envOneAt zero (suc zero) ⟩
                 → ⟨ fst E ∈ b ⟩
    envK-bounded E z hz h =
      subst (λ u → ⟨ u ∈ b ⟩)
        (sym (envOneAt-out zero (suc zero) (E ∷ z ∷ γ) h ∙ envOne-pair (fst z)))
        (sgltIn (pr (# 0) (fst z)) (prIn (# 0) (fst z) numIn hz))

  -- CONTROL 4.  The bound is not made empty by any of this.  The one
  -- instantiation the repaired hypothesis refuses is `z := B`, and it
  -- refuses it because the hierarchy already refuses `b ∈ b`.
  self-blocked : ⟨ b ∈ b ⟩ → Empty.⊥
  self-blocked = ∈-irrefl b

-- =====================================================================
-- PART 2.  CONTROL 5, THE EXTENT (C-42).
--
-- `EnvOneAgree`'s own `pairK` (src/L/Condensation.lagda.md:6751-6753)
-- has the SAME tag premise but reads a FIXED environment slot, not a
-- quantified variable.  It is a TERM under the same two record fields.
-- So the shape the refutation kills is「the tag's payload slot is the
-- quantified variable」and nothing wider.  `[LJ-1.336]` measured that
-- module at 42 lines and this control leaves it standing.
-- =====================================================================

module Extent {m : ℕ} (Kj : Fin m) (δ : S ^ suc (suc m))
  (pairK : (a c : S) → ⟨ fst a ∈ fst (lookup (suc (suc Kj)) δ) ⟩
         → ⟨ fst c ∈ fst (lookup (suc (suc Kj)) δ) ⟩
         → ⟨ fst (prʟ a c) ∈ fst (lookup (suc (suc Kj)) δ) ⟩)
  (numK0 : ⟨ fst (numeralL 0) ∈ fst (lookup (suc (suc Kj)) δ) ⟩)
  (slotIn : ⟨ fst (lookup (suc zero) δ) ∈ fst (lookup (suc (suc Kj)) δ) ⟩)
  where

  envOnePairK : (z : S) → ⟨ (z ∷ δ) ⊨ tagAtL zero 0 (suc (suc zero)) ⟩
              → ⟨ fst z ∈ fst (lookup (suc (suc Kj)) δ) ⟩
  envOnePairK z h =
    subst (λ u → ⟨ u ∈ fst (lookup (suc (suc Kj)) δ) ⟩) (sym eq2)
      (pairK (numeralL 0) (lookup (suc zero) δ) numK0 slotIn)
    where
    eq : fst z ≡ pr (# 0) (fst (lookup (suc zero) δ))
    eq = subst ⟨_⟩ (tagAtL-adequate zero 0 (suc (suc zero)) (z ∷ δ)) h

    eq2 : fst z ≡ fst (prʟ (numeralL 0) (lookup (suc zero) δ))
    eq2 = eq ∙ sym (prʟ-fst (numeralL 0) (lookup (suc zero) δ)
                   ∙ cong (λ u → pr u (fst (lookup (suc zero) δ)))
                       (numeralL-fst 0))

{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.344] THE SUPPLY.  THE TWO REPAIRED TIES, AS TERMS.
--
-- `[LJ-1.341]` proved the two pre-repair ties FALSE.  `[LJ-1.343]` landed
-- the repair.  `[LJ-1.345]` upheld both.  None of the three SUPPLIED the
-- repaired ties.  This file does.
--
-- THE TIE TYPES ARE VERBATIM from the delivered chapter:
--   `envK`     src/L/Condensation.lagda.md:6787-6789 (DefinesAgree)
--                                          :7194-7196 (LeafAgree)
--   `defPairK` src/L/Condensation.lagda.md:6790-6792 (DefinesAgree)
--                                          :7197-7199 (LeafAgree)
--
-- THE CLAIM UNDER TEST, from the brief: 「the singleton closure is TWO
-- lines from `BoundOver.pr∈λ` and `trans∈λ`」.  `KFacts` needs NO new
-- field and `BoundOver` needs no new lemma: the closure the tie wants is
-- `arityK` after `pairK`, and both are fields the record already has.
-- See `sgltK` below.
--
-- ONE agda process under GHCRTS="-A64m -I0 -M8g".

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( var; _∈̇_; _∧̇_; ∃̇_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆; ⁅_⁆s; pairing-ax; ∅ ) renaming ( module InfinitySet to Inf )
open Inf using ( #_; sucV )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ∈∈ₛ; extensionality; _⊆_ )
open import Cubical.Data.Sum using ( inl; inr )
open import Cubical.Data.Nat using ( _+_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )

module LJ-1-344.Supply344 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL-trans; IsOrd; Lset; Lset-mono )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )
open import L.Ordinal {ℓ} using ( numeral-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )

import L.Coding.Model
module GM = L.Coding.Model {ℓ}
open GM using ( tagAtL; tagAtL-adequate; prʟ; prʟ-fst )
open GM.AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

open import L.Coding.Powerset {ℓ} lem
  using ( envOneAt; envOne; envOneAt-out; envOneAt-in )

open import L.Condensation {ℓ} lem
  using ( module KFactsNS; module DefinesAgree; module KValue )
open KFactsNS

open hPropStructure 𝒮ʟ using ( S )

-- =====================================================================
-- PART 0.  THE ONE AMBIENT FACT THE TREE KEEPS PRIVATE.
--
-- `⁅ x , y ⁆ ∈ pr x y` is `inr∈⁅,⁆` at src/V/Coding.lagda.md:149-150,
-- inside that chapter's `private` block, so no consumer can name it.
-- These four lines are `[LJ-1.302]`'s, at
-- agents/tasks/LJ-1-302/ProbeLJ1302B.agda:105-108, and `[LJ-1.338]` and
-- `[LJ-1.341]` each copied them for the same reason.
-- =====================================================================

pair∈pr : (x y : V ℓ) → ⟨ ⁅ x , y ⁆ ∈ pr x y ⟩
pair∈pr x y =
  ∈∈ₛ {a = ⁅ x , y ⁆} {b = pr x y} .snd
    (pairing-ax ⁅ x ⁆s ⁅ x , y ⁆ ⁅ x , y ⁆ .snd ∣ inr refl ∣₁)

-- THE SINGLETON AS A CARRIER ELEMENT.  Every `KFacts` closure is stated
-- at `fst` of a carrier element, so a supply that must speak about
-- `⁅ x , x ⁆` needs that set AS an element.  L is transitive and
-- `⁅ x , x ⁆` is a member of `pr x x`, which `prʟ` already delivers.
sglS : S → S
sglS a = ⁅ fst a , fst a ⁆
       , isL-trans {x = fst (prʟ a a)} {y = ⁅ fst a , fst a ⁆}
           (subst (λ u → ⟨ ⁅ fst a , fst a ⁆ ∈ u ⟩) (sym (prʟ-fst a a))
             (pair∈pr (fst a) (fst a)))
           (snd (prʟ a a))

x∈pair : (x y : V ℓ) → ⟨ x ∈ ⁅ x , y ⁆ ⟩
x∈pair x y =
  ∈∈ₛ {a = x} {b = ⁅ x , y ⁆} .snd (pairing-ax x y x .snd ∣ inl refl ∣₁)

pair-only : (x d : V ℓ) → ⟨ d ∈ ⁅ x , x ⁆ ⟩ → d ≡ x
pair-only x d h = PT.rec (setIsSet d x) (λ { (inl p) → p ; (inr p) → p })
  (pairing-ax x x d .fst (∈∈ₛ {a = d} {b = ⁅ x , x ⁆} .fst h))

-- The one-entry environment IS the singleton of its only entry.  The two
-- clauses are `[LJ-1.336]`'s own, at src/L/Coding/Powerset.lagda.md:139-144,
-- read at the hierarchy instead of at the model, because that chapter
-- keeps them private too.  Copied from
-- agents/tasks/LJ-1-341/ProbeTies341.agda:122-145.
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
-- PART 1.  THE SUPPLY, FROM FOUR CLOSURE FACTS AND NOTHING ELSE.
--
-- The four are `KFacts` fields, at src/L/Condensation.lagda.md:6091,
-- :6107-6108, :6109-6110 and :6111-6112.  They are stated here as
-- MODULE PARAMETERS, never folded into a record (C-55), so the supply
-- reads at any carrier that has them and PART 2 shows the delivered
-- record hands them over.
-- =====================================================================

module TieSupply {n : ℕ} (A K : Fin n) (γ : S ^ n)
  (numK0 : ⟨ fst (numeralL 0) ∈ fst (lookup K γ) ⟩)
  (pairK : (a b : S) → ⟨ fst a ∈ fst (lookup K γ) ⟩
         → ⟨ fst b ∈ fst (lookup K γ) ⟩
         → ⟨ fst (prʟ a b) ∈ fst (lookup K γ) ⟩)
  (carrierK : (v : S) → ⟨ fst v ∈ fst (lookup A γ) ⟩
            → ⟨ fst v ∈ fst (lookup K γ) ⟩)
  (arityK : (N v : S) → ⟨ fst v ∈ fst N ⟩ → ⟨ fst N ∈ fst (lookup K γ) ⟩
          → ⟨ fst v ∈ fst (lookup K γ) ⟩) where

  private
    bnd : V ℓ
    bnd = fst (lookup K γ)

    tagged : S → S
    tagged z = prʟ (numeralL 0) z

    tagged-fst : (z : S) → fst (tagged z) ≡ pr (# 0) (fst z)
    tagged-fst z =
      prʟ-fst (numeralL 0) z ∙ cong (λ u → pr u (fst z)) (numeralL-fst 0)

    tagged∈K : (z : S) → ⟨ fst z ∈ fst (lookup A γ) ⟩ → ⟨ fst (tagged z) ∈ bnd ⟩
    tagged∈K z hz = pairK (numeralL 0) z numK0 (carrierK z hz)

  -- THE SINGLETON CLOSURE.  The brief prices it at two lines from
  -- `BoundOver.pr∈λ` and `trans∈λ`.  That price is for a closure over
  -- the AMBIENT sort, `⟨ x ∈ b ⟩ → ⟨ ⁅ x , x ⁆ ∈ b ⟩`, and the tie
  -- cannot use it: the tie's conclusion is about `fst E` for an `E : S`
  -- the tie itself quantifies over, and `KFacts` states every closure at
  -- `fst` of a carrier element.  Written at the sort the tie uses, the
  -- closure needs NO new field and NO new `BoundOver` lemma: it is
  -- `pairK` then `arityK`.
  sgltK : (a E : S) → fst E ≡ ⁅ fst a , fst a ⁆
        → ⟨ fst a ∈ bnd ⟩ → ⟨ fst E ∈ bnd ⟩
  sgltK a E q ha = arityK (prʟ a a) E mem (pairK a a ha ha)
    where
    mem : ⟨ fst E ∈ fst (prʟ a a) ⟩
    mem = subst (λ u → ⟨ fst E ∈ u ⟩) (sym (prʟ-fst a a))
            (subst (λ u → ⟨ u ∈ pr (fst a) (fst a) ⟩) (sym q)
              (pair∈pr (fst a) (fst a)))

  -- TIE 1.  Type VERBATIM from src/L/Condensation.lagda.md:6787-6789.
  envK : (E z : S) → ⟨ fst z ∈ fst (lookup A γ) ⟩
       → ⟨ (E ∷ z ∷ γ) ⊨ envOneAt zero (suc zero) ⟩
       → ⟨ fst E ∈ fst (lookup K γ) ⟩
  envK E z hz h = sgltK (tagged z) E q (tagged∈K z hz)
    where
    q : fst E ≡ ⁅ fst (tagged z) , fst (tagged z) ⁆
    q = envOneAt-out zero (suc zero) (E ∷ z ∷ γ) h
      ∙ envOne-pair (fst z)
      ∙ cong (λ u → ⁅ u , u ⁆) (sym (tagged-fst z))

  -- TIE 2.  Type VERBATIM from src/L/Condensation.lagda.md:6790-6792.
  defPairK : (E z w' : S) → ⟨ fst z ∈ fst (lookup A γ) ⟩
           → ⟨ (w' ∷ E ∷ z ∷ γ) ⊨ tagAtL zero 0 (suc (suc zero)) ⟩
           → ⟨ fst w' ∈ fst (lookup K γ) ⟩
  defPairK E z w' hz h = subst (λ u → ⟨ u ∈ bnd ⟩) (sym q) (tagged∈K z hz)
    where
    q : fst w' ≡ fst (tagged z)
    q = subst ⟨_⟩ (tagAtL-adequate zero 0 (suc (suc zero)) (w' ∷ E ∷ z ∷ γ)) h
      ∙ sym (tagged-fst z)

  -- NON-VACUITY, PART 1.  The satisfaction premise is REACHED from a
  -- bare set equation, so it is not a formula nobody can meet.
  -- `envOneAt-in` is the chapter's own converse, at
  -- src/L/Coding/Powerset.lagda.md:146-147.
  envK-live : (E z : S) → ⟨ fst z ∈ fst (lookup A γ) ⟩
            → fst E ≡ envOne (fst z)
            → ⟨ fst E ∈ fst (lookup K γ) ⟩
  envK-live E z hz q = envK E z hz (envOneAt-in zero (suc zero) (E ∷ z ∷ γ) q)

  defPairK-live : (E z w' : S) → ⟨ fst z ∈ fst (lookup A γ) ⟩
                → fst w' ≡ pr (# 0) (fst z)
                → ⟨ fst w' ∈ fst (lookup K γ) ⟩
  defPairK-live E z w' hz q = defPairK E z w' hz
    (subst ⟨_⟩ (sym (tagAtL-adequate zero 0 (suc (suc zero)) (w' ∷ E ∷ z ∷ γ))) q)

  -- NON-VACUITY, PART 2.  A REAL INHABITANT of each premise, built and
  -- not assumed.  `liveE z` is the one-entry environment over `z` AS AN
  -- ELEMENT OF THE CARRIER SORT: its set is `⁅ a₀ , a₀ ⁆` and its `isL`
  -- component comes from the transitivity of L applied to `pr a₀ a₀`,
  -- which is `fst` of a carrier element.  So nothing here assumes that
  -- an `E` exists; it is exhibited.
  liveE : S → S
  liveE z = sglS (tagged z)

  -- The singleton closure again, in the form the residue probe needs.
  sglK : (a : S) → ⟨ fst a ∈ bnd ⟩ → ⟨ fst (sglS a) ∈ bnd ⟩
  sglK a ha = sgltK a (sglS a) refl ha

  liveE-eq : (z : S) → fst (liveE z) ≡ envOne (fst z)
  liveE-eq z = sym (envOne-pair (fst z)
                   ∙ cong (λ u → ⁅ u , u ⁆) (sym (tagged-fst z)))

  -- The `envK` premise, INHABITED at that witness, at every `z`.
  live-envK-premise : (z : S)
                    → ⟨ (liveE z ∷ z ∷ γ) ⊨ envOneAt zero (suc zero) ⟩
  live-envK-premise z =
    envOneAt-in zero (suc zero) (liveE z ∷ z ∷ γ) (liveE-eq z)

  -- The `defPairK` premise, INHABITED at the tagged pair, at every `z`.
  live-defPairK-premise : (E z : S)
                        → ⟨ (tagged z ∷ E ∷ z ∷ γ) ⊨ tagAtL zero 0 (suc (suc zero)) ⟩
  live-defPairK-premise E z = subst ⟨_⟩
    (sym (tagAtL-adequate zero 0 (suc (suc zero)) (tagged z ∷ E ∷ z ∷ γ)))
    (tagged-fst z)

  -- BOTH PREMISES AT ONCE, and the tie FIRES.  The one premise this
  -- needs and cannot build is that the carrier slot has a member; that
  -- is the repair's own hypothesis and it is stated here as ONE named
  -- parameter, never hidden inside a record (C-55).
  module Live (u : S) (hu : ⟨ fst u ∈ fst (lookup A γ) ⟩) where

    envK-fires : ⟨ fst (liveE u) ∈ fst (lookup K γ) ⟩
    envK-fires = envK (liveE u) u hu (live-envK-premise u)

    defPairK-fires : ⟨ fst (tagged u) ∈ fst (lookup K γ) ⟩
    defPairK-fires =
      defPairK (liveE u) u (tagged u) hu (live-defPairK-premise (liveE u) u)

-- =====================================================================
-- PART 2.  THE DELIVERED RECORD HANDS THE FOUR OVER.
--
-- `KFacts` is src/L/Condensation.lagda.md:6076-6112, imported, never
-- restated.  So the supply costs the chapter NO new field.
-- =====================================================================

module FromRecord {n : ℕ}
  (A K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 : Fin n) (γ : S ^ n)
  (f : KFacts A K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 γ) where

  open KFacts f using ( numK0; pairK; carrierK; arityK )

  open TieSupply A K γ numK0 pairK carrierK arityK public

-- =====================================================================
-- PART 3.  THE FIT.  The consumer accepts the supply, positionally.
--
-- `DefinesAgree` (src/L/Condensation.lagda.md:6778-6796) is the module
-- that eats both ties.  Its carrier slot is `w` and `KFacts`'s carrier
-- index `A` is the same slot, so the record and the tie agree by
-- construction.  `N0eq` is `tagEq0` and `numK` is `numK0`.
-- =====================================================================

module Fit {m : ℕ} (x w v K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 : Fin m)
  (γ : S ^ m)
  (f : KFacts w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 γ)
  (satK : (z : S) → ⟨ (z ∷ γ) ⊨
             ((var zero ∈̇ var (suc w)) ∧̇
              ∃̇ (envOneAt zero (suc zero) ∧̇ (var zero ∈̇ var (suc (suc v))))) ⟩
         → ⟨ fst z ∈ fst (lookup K γ) ⟩) where

  open FromRecord w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 γ f
  open KFacts f using ( tagEq0; numK0 )

  module DA = DefinesAgree x w v K N0 γ tagEq0 numK0 envK defPairK satK

  -- THE CONSUMER'S OWN TWO DIRECTIONS, FORCED.  Nothing below is my
  -- statement: `fwd` is `DefinesAgree`'s at :6806-6819, which applies
  -- my `defPairK` at :6819, and `bwd` is at :6821-6834, which applies
  -- my `envK` at :6828.  Both elaborate, so the supply is what the
  -- consumer eats and not merely what has the right type.
  fit-fwd : (z : S) → ⟨ (z ∷ γ) ⊨ DA.bodyB ⟩ → ⟨ (z ∷ γ) ⊨ DA.bodyM ⟩
  fit-fwd = DA.fwd

  fit-bwd : (z : S) → ⟨ (z ∷ γ) ⊨ DA.bodyM ⟩ → ⟨ (z ∷ γ) ⊨ DA.bodyB ⟩
  fit-bwd = DA.bwd

-- =====================================================================
-- PART 4.  THE SECOND INDEX FORM, AT `LeafAgree`.
--
-- `LeafAgree` (src/L/Condensation.lagda.md:7115-7202) states the same
-- two ties under `suc (suc (suc w))` and `suc (suc (suc K))` and hands
-- them to `DefinesAgree` at :7207-7209.  The two types below are
-- VERBATIM from :7194-7199 and each is defined by the supply alone.
-- =====================================================================

module LeafFit {n : ℕ}
  (w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 : Fin (5 + n))
  (γ : S ^ (8 + n))
  (f : KFacts {8 + n} (suc (suc (suc w))) (suc (suc (suc K)))
         (suc (suc (suc N0))) (suc (suc (suc N1)))
         (suc (suc (suc N2))) (suc (suc (suc N3)))
         (suc (suc (suc N4))) (suc (suc (suc N5)))
         (suc (suc (suc N6))) (suc (suc (suc N7)))
         (suc (suc (suc N8))) (suc (suc (suc N9)))
         (suc (suc (suc N10))) (suc (suc (suc N11))) γ) where

  open FromRecord (suc (suc (suc w))) (suc (suc (suc K)))
         (suc (suc (suc N0))) (suc (suc (suc N1)))
         (suc (suc (suc N2))) (suc (suc (suc N3)))
         (suc (suc (suc N4))) (suc (suc (suc N5)))
         (suc (suc (suc N6))) (suc (suc (suc N7)))
         (suc (suc (suc N8))) (suc (suc (suc N9)))
         (suc (suc (suc N10))) (suc (suc (suc N11))) γ f

  envK-leaf : (E z : S) → ⟨ fst z ∈ fst (lookup (suc (suc (suc w))) γ) ⟩
            → ⟨ (E ∷ z ∷ γ) ⊨ envOneAt zero (suc zero) ⟩
            → ⟨ fst E ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
  envK-leaf = envK

  defPairK-leaf : (E z w' : S) → ⟨ fst z ∈ fst (lookup (suc (suc (suc w))) γ) ⟩
                → ⟨ (w' ∷ E ∷ z ∷ γ) ⊨ tagAtL zero 0 (suc (suc zero)) ⟩
                → ⟨ fst w' ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
  defPairK-leaf = defPairK

-- =====================================================================
-- PART 5.  THE END-TO-END WIRING, AND THE NON-VACUITY THAT MEASURES.
--
-- `module KValue` (src/L/Condensation.lagda.md:7277-7330) builds the one
-- `KFacts` VALUE and `[LJ-1.338]` measured it has ZERO consumers
-- anywhere in `src/`.  It gets its first consumer here.  Nothing below
-- restates a field: the record arrives from the chapter and the two ties
-- come out.
--
-- The frame parameters are `KValue`'s own six.  ONE hypothesis is mine,
-- `#1∈γ`, and it says the carrier stage is at least 1.  It is what makes
-- the carrier NON-EMPTY, and without a non-empty carrier the repaired
-- tie would be true because nothing meets it.  That is the failure this
-- whole episode is about (C-45).
-- =====================================================================

module KWire (lam : V ℓ) (ordλ : IsOrd lam)
             (succλ : (d : V ℓ) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩)
             (∅∈λ : ⟨ ∅ ∈ lam ⟩)
             (gam : V ℓ) (ordγ : IsOrd gam) (γ∈λ : ⟨ gam ∈ lam ⟩)
             (#1∈γ : ⟨ (# 1) ∈ gam ⟩) where

  module KV = KValue lam ordλ succλ ∅∈λ gam ordγ γ∈λ

  open FromRecord KV.iA KV.iK KV.i0 KV.i1 KV.i2 KV.i3 KV.i4 KV.i5
         KV.i6 KV.i7 KV.i8 KV.i9 KV.i10 KV.i11 KV.Kenv KV.facts public

  -- THE CARRIER IS INHABITED.  `# 0` is an ordinal, so it is in the next
  -- stage, and the carrier stage is above that.
  zero∈carrier : ⟨ fst (numeralL 0) ∈ fst (lookup KV.iA KV.Kenv) ⟩
  zero∈carrier = subst (λ u → ⟨ u ∈ Lset gam ⟩) (sym (numeralL-fst 0))
    (Lset-mono {α = gam} {β = # 1} #1∈γ
      {x = # 0} (ord∈Lset-suc (# 0) (numeral-ord 0)))

  -- BOTH TIES FIRE, WITH EVERY PREMISE DISCHARGED.
  module Fires = Live (numeralL 0) zero∈carrier

  envK-fires : ⟨ fst (liveE (numeralL 0)) ∈ Lset lam ⟩
  envK-fires = Fires.envK-fires

  defPairK-fires : ⟨ pr (# 0) (# 0) ∈ Lset lam ⟩
  defPairK-fires = subst (λ u → ⟨ u ∈ Lset lam ⟩)
    (prʟ-fst (numeralL 0) (numeralL 0)
      ∙ cong₂ pr (numeralL-fst 0) (numeralL-fst 0))
    Fires.defPairK-fires

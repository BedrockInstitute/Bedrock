{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.338] PROBE 2.  THE THIRD SITE: `LeafAgree`'s TIE SUPPLY AT THE
-- AMBIENT CARRIER.
--
-- `[LJ-1.302]` measured site 1, `DomainAgree`, at 51 lines.
-- `[LJ-1.336]` measured site 2, `EnvOneAgree`, at 42 lines, and it
-- measured the sharing between them at ZERO.  This file measures site 3.
--
-- `LeafAgree` (src/L/Condensation.lagda.md:7107-7243) is the UNION site:
-- it proves nothing about its own ties and hands them to
-- `WitnessAgree`, `KeyAgree`, `SatGraphAgree` and `DefinesAgree` at
-- :7191-7209.  So one measurement here prices four of the five
-- unmeasured modules.
--
-- THE ENVIRONMENT.  `n := 9`, so the indices are `Fin 14` and the
-- environment is `S ^ 17`.  The last fourteen slots are `KValue`'s own
-- `Kenv`, so the `KFacts` tie is the transported `KValue` lifted three
-- times by `KFactsCons`, which is what `SatGraphAgree.lift3` does at
-- :6903-6939.
--
-- WHAT THIS FILE SUPPLIES AND WHAT IT LEAVES.  Every tie the two
-- measured supplies discharge is GIVEN here.  Every tie they do not
-- discharge stays a PARAMETER of `Supply`, with its name, so the residue
-- is named and not hidden.
--
-- ONE agda process under GHCRTS="-A64m -I0 -M8g".

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

open import FOL.ZFStructure using ( module hPropStructure; _↾_ )
open import FOL.Syntax using ( Formula; var; _∈̇_; _≐_; _∧̇_; ∃̇_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆; ∅ ) renaming ( module InfinitySet to Inf )
open Inf using ( #_; sucV )
open import Cubical.Data.Unit using ( tt* )
open import Cubical.Data.Sigma using ( _×_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

import LJ-1-338.ProbeKValue338

module LJ-1-338.ProbeLeaf338 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( Lset; IsOrd )

import LJ-1-184.ProbeLJ1184A {ℓ} as P184
import LJ-1-297.ProbeLJ1297A {ℓ} lem as P1297A
import LJ-1-297.ProbeLJ1297C {ℓ} as P1297C
import LJ-1-302.ProbeLJ1302B {ℓ} lem as P1302B
module PKV = LJ-1-338.ProbeKValue338 {ℓ} lem
module GD = PKV.GD

module A = P184.Ambient
open P1297C using ( absFull )

open hPropStructure (𝒮ᵥ ↾ P1297A.Full) using ( S )
open GD.W1.KFactsNS using ( KFacts )
open GD.W1.KFactsNS.KFacts
open GD.W1 using ( KFactsCons; shapedAt )
open GD.W1.GM using ( closedAt; domAt; appAt; tagAtL; tagAtL-adequate
                    ; prʟ; prʟ-fst )
open GD.W1.GM.AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )
open GD using ( module SatGraphB; twelveAt; envOneAt; DefBody; DefBodyB )

-- The ambient reading, `[LJ-1.297]`'s transport, as `[LJ-1.302]` and
-- `[LJ-1.336]` both use it.  Seven lines, and they are the SAME seven at
-- every site.
toAmb : ∀ {n} (φ : Formula A.R.SC n) (γ' : A.R.SC ^ n)
      → ⟨ γ' ⊨ φ ⟩ → ⟨ A.ambient γ' φ ⟩
toAmb φ γ' = subst ⟨_⟩ (absFull φ γ')

fromAmb : ∀ {n} (φ : Formula A.R.SC n) (γ' : A.R.SC ^ n)
        → ⟨ A.ambient γ' φ ⟩ → ⟨ γ' ⊨ φ ⟩
fromAmb φ γ' = subst ⟨_⟩ (sym (absFull φ γ'))

-- The sixteen indices.  Fourteen are distinct and point at `Kenv`'s
-- fourteen slots after the three-slot leaf frame; `t0` and `t1` are only
-- read by `SatGraphB.twelveB`, which this file takes as a hypothesis.
w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 : Fin 14
w   = zero
K   = suc zero
N0  = suc (suc zero)
N1  = suc (suc (suc zero))
N2  = suc (suc (suc (suc zero)))
N3  = suc (suc (suc (suc (suc zero))))
N4  = suc (suc (suc (suc (suc (suc zero)))))
N5  = suc (suc (suc (suc (suc (suc (suc zero))))))
N6  = suc (suc (suc (suc (suc (suc (suc (suc zero)))))))
N7  = suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
N8  = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
N9  = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))
N10 = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))
N11 = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))
t0  = zero
t1  = suc zero

-- =====================================================================
-- THE SUPPLY.  Site 3, at a concrete ambient environment.
--
-- THE PARAMETERS AFTER `γ∈λ` ARE THE RESIDUE.  Each is a tie of
-- `LeafAgree` that NEITHER measured supply discharges, and each carries
-- the reason above it.  `twelve-out` and `twelve-back` are not ties at
-- all: `[LJ-1.302]:200-203` classes them as BS-to-machine readings of
-- the twelve, and `[LJ-1.298]` priced that port separately.
-- =====================================================================
module Supply (lam : V ℓ) (ordλ : IsOrd lam)
              (succλ : (d : V ℓ) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩)
              (∅∈λ : ⟨ ∅ ∈ lam ⟩)
              (gam : V ℓ) (ordγ : IsOrd gam) (γ∈λ : ⟨ gam ∈ lam ⟩)
              -- RESIDUE 1.  The arity of a binary code is a numeral.
              -- This is a fact about the CODE SET, not about the bound,
              -- so no closure lemma proves it.
              (wArNum : (w' : S) → (k : ℕ) → (c ar a b : S)
                      → ⟨ fst c ∈ fst w' ⟩
                      → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
                      → ∥ Σ[ m ∈ ℕ ] (fst ar ≡ # m) ∥₁)
              -- RESIDUE 2.  The same, for a unary code.
              (wUnArNum : (w' : S) → (k : ℕ) → (c ar a : S)
                        → ⟨ fst c ∈ fst w' ⟩
                        → fst c ≡ pr (fst ar) (pr (# k) (fst a))
                        → ∥ Σ[ m ∈ ℕ ] (fst ar ≡ # m) ∥₁)
              where

  module B = PKV.Bound lam ordλ succλ ∅∈λ
  module KV = PKV.KValue lam ordλ succλ ∅∈λ gam ordγ γ∈λ
  module P1302 = P1302B.Supply lam gam gam γ∈λ γ∈λ

  -- THE THREE LEAF SLOTS.  Slot 1 is the code `c`, and `keyValK` reads
  -- it, so it must be a real pair inside the bound.  The other two are
  -- free and take a numeral.
  e0 e1 e2 : S
  e0 = PKV.numeralL 0
  e1 = prʟ (PKV.numeralL 1) (PKV.numeralL 0)
  e2 = PKV.numeralL 0

  e1∈K : ⟨ fst e1 ∈ Lset lam ⟩
  e1∈K = B.prʟ∈λ (PKV.numeralL 1) (PKV.numeralL 0) (B.num∈λ 1) (B.num∈λ 0)

  γ : S ^ 17
  γ = e0 ∷ e1 ∷ e2 ∷ KV.Kenv

  -- THE `KFacts` TIE.  `KValue`'s value, lifted three times.  Nothing is
  -- re-proved: `KFactsCons` is the chapter's own lift, at :6119-6157.
  fL : KFacts {17} (suc (suc (suc w))) (suc (suc (suc K)))
         (suc (suc (suc N0))) (suc (suc (suc N1)))
         (suc (suc (suc N2))) (suc (suc (suc N3)))
         (suc (suc (suc N4))) (suc (suc (suc N5)))
         (suc (suc (suc N6))) (suc (suc (suc N7)))
         (suc (suc (suc N8))) (suc (suc (suc N9)))
         (suc (suc (suc N10))) (suc (suc (suc N11))) γ
  fL = KFactsCons (suc (suc KV.iA)) (suc (suc KV.iK))
         (suc (suc KV.i0)) (suc (suc KV.i1)) (suc (suc KV.i2))
         (suc (suc KV.i3)) (suc (suc KV.i4)) (suc (suc KV.i5))
         (suc (suc KV.i6)) (suc (suc KV.i7)) (suc (suc KV.i8))
         (suc (suc KV.i9)) (suc (suc KV.i10)) (suc (suc KV.i11))
         (e1 ∷ e2 ∷ KV.Kenv) e0
         (KFactsCons (suc KV.iA) (suc KV.iK)
           (suc KV.i0) (suc KV.i1) (suc KV.i2) (suc KV.i3)
           (suc KV.i4) (suc KV.i5) (suc KV.i6) (suc KV.i7)
           (suc KV.i8) (suc KV.i9) (suc KV.i10) (suc KV.i11)
           (e2 ∷ KV.Kenv) e1 (KV.consed e2))

  -- THE ONE SHARED BLOCK, AND IT IS `[LJ-1.302]`'s.  Three parameter-free
  -- pair lemmas from site 1, plus `Bound`'s transitivity.  Every
  -- downward tie below is two calls of this.
  pairDown : (x y : V ℓ) → ⟨ pr x y ∈ Lset lam ⟩
           → ⟨ x ∈ Lset lam ⟩ × ⟨ y ∈ Lset lam ⟩
  pairDown x y h =
    ( B.trans∈λ (P1302.x∈pair x y) pairIn
    , B.trans∈λ (P1302.y∈pair x y) pairIn )
    where
    pairIn : ⟨ ⁅ x , y ⁆ ∈ Lset lam ⟩
    pairIn = B.trans∈λ (P1302.pair∈pr x y) h

  -- =====================================================================
  -- SUPPLIED TIE 1.  `wEntryK`.  Type VERBATIM from :7135-7138.
  -- =====================================================================
  wEntryK : (w' : S) → ⟨ fst w' ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
          → (x' y : S) → ⟨ pr (fst x') (fst y) ∈ fst w' ⟩
          → ⟨ fst x' ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
            × ⟨ fst y ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
  wEntryK w' hw x' y h = pairDown (fst x') (fst y) (B.trans∈λ h hw)

  -- =====================================================================
  -- SUPPLIED TIE 2.  `wCodesK`.  Type VERBATIM from :7122-7128.  Three
  -- of the four conjuncts come from the closure; the fourth is
  -- RESIDUE 1.
  -- =====================================================================
  wCodesK : (w' : S) → ⟨ fst w' ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
          → (k : ℕ) → (c ar a b : S) → ⟨ fst c ∈ fst w' ⟩
          → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
          → ⟨ fst ar ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
            × ⟨ fst a ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
            × ⟨ fst b ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
          × ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
  wCodesK w' hw k c ar a b hc eq =
    ( fst p1 , ( fst p3 , ( snd p3 , wArNum w' k c ar a b hc eq ) ) )
    where
    c∈ : ⟨ fst c ∈ Lset lam ⟩
    c∈ = B.trans∈λ hc hw
    p1 = pairDown (fst ar) (pr (# k) (pr (fst a) (fst b)))
           (subst (λ v → ⟨ v ∈ Lset lam ⟩) eq c∈)
    p2 = pairDown (# k) (pr (fst a) (fst b)) (snd p1)
    p3 = pairDown (fst a) (fst b) (snd p2)

  -- =====================================================================
  -- SUPPLIED TIE 3.  `wUnCodesK`.  Type VERBATIM from :7129-7134.
  -- =====================================================================
  wUnCodesK : (w' : S) → ⟨ fst w' ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
            → (k : ℕ) → (c ar a : S) → ⟨ fst c ∈ fst w' ⟩
            → fst c ≡ pr (fst ar) (pr (# k) (fst a))
            → ⟨ fst ar ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
              × ⟨ fst a ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
          × ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
  wUnCodesK w' hw k c ar a hc eq =
    ( fst p1 , ( snd p2 , wUnArNum w' k c ar a hc eq ) )
    where
    c∈ : ⟨ fst c ∈ Lset lam ⟩
    c∈ = B.trans∈λ hc hw
    p1 = pairDown (fst ar) (pr (# k) (fst a))
           (subst (λ v → ⟨ v ∈ Lset lam ⟩) eq c∈)
    p2 = pairDown (# k) (fst a) (snd p1)

  -- =====================================================================
  -- SUPPLIED TIES 4 to 7.  The graph frame reads the SAME three ties at
  -- the `d` slot, so each is one call of the witness-frame tie.  Types
  -- VERBATIM from :7145-7170.
  -- =====================================================================
  gCodesK : (d e f : S) → ⟨ fst d ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
          → (k : ℕ) → (c ar a b : S)
          → ⟨ fst c ∈ fst (lookup (suc (suc zero)) (f ∷ e ∷ d ∷ γ)) ⟩
          → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
          → ⟨ fst ar ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
            × ⟨ fst a ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
            × ⟨ fst b ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
          × ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
  gCodesK d e f hd = wCodesK d hd

  gUnCodesK : (d e f : S) → ⟨ fst d ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
            → (k : ℕ) → (c ar a : S)
            → ⟨ fst c ∈ fst (lookup (suc (suc zero)) (f ∷ e ∷ d ∷ γ)) ⟩
            → fst c ≡ pr (fst ar) (pr (# k) (fst a))
            → ⟨ fst ar ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
              × ⟨ fst a ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
          × ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
  gUnCodesK d e f hd = wUnCodesK d hd

  gEntryK : (d e f : S) → ⟨ fst d ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
          → (x' y : S) → ⟨ pr (fst x') (fst y) ∈ fst (lookup (suc (suc zero)) (f ∷ e ∷ d ∷ γ)) ⟩
          → ⟨ fst x' ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
            × ⟨ fst y ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
  gEntryK d e f hd = wEntryK d hd

  domEntryK : (d e f : S) → ⟨ fst e ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
            → (x' y : S) → ⟨ pr (fst x') (fst y) ∈ fst (lookup (suc zero) (f ∷ e ∷ d ∷ γ)) ⟩
            → ⟨ fst x' ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
              × ⟨ fst y ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
  domEntryK d e f he = wEntryK e he

  -- =====================================================================
  -- SUPPLIED TIE 8.  `domK`, one call of `KFacts.arityK`.  Type VERBATIM
  -- from :7168-7170.
  -- =====================================================================
  domK : (d e f : S) → ⟨ fst d ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
       → (x : S) → ⟨ fst x ∈ fst (lookup (suc (suc zero)) (f ∷ e ∷ d ∷ γ)) ⟩
       → ⟨ fst x ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
  domK d e f hd x hx = arityK fL d x hx hd

  -- =====================================================================
  -- SUPPLIED TIE 9.  `keyValK`.  The code slot is inside the bound, so
  -- the tag reading and one downward step give the value.  Type VERBATIM
  -- from :7181-7182.
  -- =====================================================================
  keyValK : (t : S) → ⟨ (t ∷ γ) ⊨ tagAtL (suc (suc zero)) 1 zero ⟩
          → ⟨ fst t ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
  keyValK t h = snd (pairDown (# 1) (fst t) prIn)
    where
    eq : fst e1 ≡ pr (# 1) (fst t)
    eq = subst ⟨_⟩ (tagAtL-adequate (suc (suc zero)) 1 zero (t ∷ γ)) h
    prIn : ⟨ pr (# 1) (fst t) ∈ Lset lam ⟩
    prIn = subst (λ v → ⟨ v ∈ Lset lam ⟩) eq e1∈K

  -- NON-VACUITY OF TIE 9.  The hypothesis is INHABITED at this
  -- environment: the numeral zero satisfies it.  Without this line the
  -- tie could be true because nothing meets it.
  keyValK-live : ⟨ (PKV.numeralL 0 ∷ γ) ⊨ tagAtL (suc (suc zero)) 1 zero ⟩
  keyValK-live = subst ⟨_⟩
    (sym (tagAtL-adequate (suc (suc zero)) 1 zero (PKV.numeralL 0 ∷ γ)))
    (prʟ-fst (PKV.numeralL 1) (PKV.numeralL 0))

  -- =====================================================================
  -- SUPPLIED TIE 10.  `satK`, one call of `KFacts.carrierK`: the `w`
  -- slot IS the record's carrier slot.  Type VERBATIM from :7187-7189.
  -- =====================================================================
  satK : (z : S) → ⟨ (z ∷ γ) ⊨ ((var zero ∈̇ var (suc (suc (suc (suc w)))))
           ∧̇ ∃̇ (envOneAt zero (suc zero) ∧̇ (var zero ∈̇ var (suc (suc zero))))) ⟩
       → ⟨ fst z ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
  satK z h = carrierK fL z (fst h)

  -- =====================================================================
  -- THE RESIDUE, AND THE INSTANTIATION.
  --
  -- The six parameters below are the ties NEITHER measured supply
  -- discharges, plus the two twelve readings, which are not ties.  Each
  -- type is VERBATIM from the chapter's telescope.  With them, the third
  -- site's module is a TERM at the ambient carrier and its two
  -- directions cross to the ambient reading.
  -- =====================================================================
  module Leaf
    -- RESIDUE 3.  The witness set is inside the bound.  The hypothesis
    -- puts the CODE inside `w'`, which is downward; the conclusion is
    -- upward, and no closure lemma climbs it.
    (witK : (w' : S) → ⟨ (w' ∷ γ) ⊨ ((var (suc (suc zero)) ∈̇ var zero)
                 ∧̇ (closedAt zero ∧̇ shapedAt zero (suc (suc (suc (suc w)))))) ⟩
           → ⟨ fst w' ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
    -- NOT A TIE.  `[LJ-1.302]:200-203` classes the two twelve readings
    -- as BS-to-machine work, priced separately at about 180 lines.
    (twelve-out : (d e f : S) → ⟨ (f ∷ e ∷ d ∷ γ) ⊨ twelveAt (suc (suc zero)) (suc zero) zero ⟩
                → ⟨ (f ∷ e ∷ d ∷ γ) ⊨ SatGraphB.twelveB {9} w K N0 N1 N2 N3 N4 N5
                                             N6 N7 N8 N9 N10 N11 t0 t1 ⟩)
    (twelve-back : (d e f : S) → ⟨ (f ∷ e ∷ d ∷ γ) ⊨ SatGraphB.twelveB {9} w K N0 N1 N2 N3 N4 N5
                                              N6 N7 N8 N9 N10 N11 t0 t1 ⟩
                 → ⟨ (f ∷ e ∷ d ∷ γ) ⊨ twelveAt (suc (suc zero)) (suc zero) zero ⟩)
    -- RESIDUE 4.  The clause set and the graph are inside the bound.
    -- The third component is derivable here, because the hypothesis
    -- equates `f` with the carrier slot; the first two are not.
    (graphWitK : (d e f : S) → ⟨ (f ∷ e ∷ d ∷ γ) ⊨
                 (var zero ≐ var (suc (suc (suc (suc (suc (suc w)))))))
                 ∧̇ (closedAt (suc (suc zero))
                   ∧̇ (domAt (suc zero) (suc (suc zero))
                     ∧̇ (appAt (suc zero) (suc (suc (suc (suc zero))))
                              (suc (suc (suc zero)))
                       ∧̇ twelveAt (suc (suc zero)) (suc zero) zero))) ⟩
           → ⟨ fst d ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
             × ⟨ fst e ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
             × ⟨ fst f ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
    -- RESIDUE 5.  The one-entry environment is inside the bound.  Its
    -- entry `z` carries NO hypothesis, so the tie is upward from an
    -- unbounded set.
    (envK : (E z : S) → ⟨ (E ∷ z ∷ γ) ⊨ envOneAt zero (suc zero) ⟩
           → ⟨ fst E ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
    -- RESIDUE 6.  The tagged pair over that same unbounded `z`.
    (defPairK : (E z w' : S) → ⟨ (w' ∷ E ∷ z ∷ γ) ⊨ tagAtL zero 0 (suc (suc zero)) ⟩
               → ⟨ fst w' ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
    where

    module LA = GD.LeafAgree {9} w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 γ
                  fL witK wCodesK wUnCodesK wEntryK twelve-out twelve-back
                  gCodesK gUnCodesK gEntryK domEntryK domK graphWitK
                  keyValK envK defPairK satK

    out-amb : ⟨ A.ambient γ (DefBody {14} w) ⟩
            → ⟨ A.ambient γ (DefBodyB w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1) ⟩
    out-amb h = toAmb (DefBodyB w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1) γ
      (LA.out (fromAmb (DefBody {14} w) γ h))

    back-amb : ⟨ A.ambient γ (DefBodyB w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1) ⟩
             → ⟨ A.ambient γ (DefBody {14} w) ⟩
    back-amb h = toAmb (DefBody {14} w) γ
      (LA.back (fromAmb (DefBodyB w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1) γ h))

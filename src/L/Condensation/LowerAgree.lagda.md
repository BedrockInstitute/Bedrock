# The lower agreement

<!--en-->
The lower agreement is the conjunction of the first six row agreements:
membership, equality, conjunction, disjunction, implication and negation.
It states the forty-three site facts those rows use at an abstract
environment and proves both directions against the twelve-row target.
<!--zh-->
下位一致是前六行一致式的合取：成员、相等、合取、析取、蕴含与否定。它把这六行用到的四十三个场地事实陈述于一个抽象环境，并对十二行目标证明两个方向。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Condensation.LowerAgree {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; _∧̇_ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Axioms.Numerals {ℓ} using ( numeralL )
open import L.Coding.Model {ℓ}
  using ( prʟ; prʟ-fst; envSetAt; envOverAt; tmValAt; subValAt
        ; memClauseAt; eqClauseAt; andClauseAt; orClauseAt
        ; impClauseAt; negClauseAt )
open import L.Coding.Graph {ℓ} lem using ( twelveAt )
open import L.Condensation {ℓ} lem using
  ( envHypB2; module Mem; module Eq; module And; module Or; module Imp
  ; module Neg; module MemAgree; module EqAgree; module AndAgree
  ; module OrAgree; module ImpAgree; module NegAgree )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet using ( #_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- perf: someEnv's type re-elaborated the built envHypB2 tree at every
-- module application (heap wall, [LJ-1.72]); the named type checks the
-- name instead.  The And and Or rows are its only consumers.
someEnvDef : {n : ℕ} (K : Fin (5 + n)) (γ : S ^ (11 + n)) → Type (ℓ-suc ℓ)
someEnvDef {n} K γ =
  (ya yc b a ar c : S) → ⟨ fst ya ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
  → ⟨ fst yc ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
  → ⟨ fst ar ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
  → Σ S (λ E → ⟨ fst E ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
    × ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ envHypB2 {11 + n} zero (suc (suc (suc (suc (suc (suc K)))))) ⟩)

-- THE TIED KEY-NEG FACT, derived once from pairK ([LJ-1.109]
-- TiesSupplied).  The Neg row's keyK conclusion is the hierarchy pair
-- pr (fst ar) (fst a); pairK gives the L-pair prʟ ar a, and prʟ-fst
-- transports.  Generic in the K slot and gamma, so LowerAgree and
-- TwelveAgree instantiate the same derivation (DD4).
module KeyNegTies {m : ℕ} (K : Fin m) (γ : S ^ m)
  (pairK : (a b : S) → ⟨ fst a ∈ fst (lookup K γ) ⟩
           → ⟨ fst b ∈ fst (lookup K γ) ⟩
           → ⟨ fst (prʟ a b) ∈ fst (lookup K γ) ⟩) where

  key-neg-tied : (ar a : S) → ⟨ fst ar ∈ fst (lookup K γ) ⟩
               → ⟨ fst a ∈ fst (lookup K γ) ⟩
               → ⟨ pr (fst ar) (fst a) ∈ fst (lookup K γ) ⟩
  key-neg-tied ar a arK aK =
    subst (λ w → ⟨ w ∈ fst (lookup K γ) ⟩) (prʟ-fst ar a)
      (pairK ar a arK aK)

-- THE FRAME'S FACT BLOCK, as ONE record rather than 37 telescope
-- hypotheses.  `[LJ-1.62]` states the reason at `src/L/Condensation.lagda.md`
-- :5990-5994, and these masters never got it: a module telescope is prepended
-- to the STORED TYPE of every definition inside the module, and Agda's
-- `DeadCode.DeadCodeReachable` pass then walks those stored types once per
-- definition.
--
-- MEASURED by `[LJ-1.158]`, a controlled pair of probes over THIS telescope,
-- two runs each side: `DeadCode` 2,689 ms to 26 ms and the probe file
-- 7,243 ms to 3,726, minus 49 percent (probes L1 and L2).
--
-- ALL 37 HYPOTHESES ARE FIELDS HERE, and the reason is a name this master
-- does not have.  P-x says a record field type may not name a transparent
-- construction of the ambient set theory, and the one such name in this
-- family is `sucV`.  The lower rows never use the successor closure, so this
-- master's `open InfinitySet` at :40 takes `#_` alone and no field can carry
-- it.  `UpperAgree` and `TwelveAgree` DO carry `sucK` and both keep it in the
-- telescope.
record LFacts {n : ℕ}
  (N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K : Fin (5 + n))
  (γ : S ^ (11 + n)) : Type (ℓ-suc ℓ) where
  field
    tagEq0 : fst (lookup (suc (suc (suc (suc (suc (suc N0)))))) γ) ≡ fst (numeralL 0)
    tagEq1 : fst (lookup (suc (suc (suc (suc (suc (suc N1)))))) γ) ≡ fst (numeralL 1)
    tagEq2 : fst (lookup (suc (suc (suc (suc (suc (suc N2)))))) γ) ≡ fst (numeralL 2)
    tagEq3 : fst (lookup (suc (suc (suc (suc (suc (suc N3)))))) γ) ≡ fst (numeralL 3)
    tagEq4 : fst (lookup (suc (suc (suc (suc (suc (suc N4)))))) γ) ≡ fst (numeralL 4)
    tagEq5 : fst (lookup (suc (suc (suc (suc (suc (suc N5)))))) γ) ≡ fst (numeralL 5)
    numK0 : ⟨ fst (numeralL 0) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
    numK1 : ⟨ fst (numeralL 1) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
    numK2 : ⟨ fst (numeralL 2) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
    numK3 : ⟨ fst (numeralL 3) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
    numK4 : ⟨ fst (numeralL 4) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
    numK5 : ⟨ fst (numeralL 5) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
    innerK : (k : ℕ) (p : S) → ⟨ fst p ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
              → ⟨ fst (prʟ (numeralL k) p) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
    pairK : (a b : S) → ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
              → ⟨ fst b ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
              → ⟨ fst (prʟ a b) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
    codesK : (k : ℕ) (c ar a b : S) → ⟨ fst c ∈ fst (lookup (suc (suc zero)) γ) ⟩
             → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
             → ⟨ fst ar ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
               × ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
               × ⟨ fst b ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
    codesK-un : (k : ℕ) (c ar a : S) → ⟨ fst c ∈ fst (lookup (suc (suc zero)) γ) ⟩
                → fst c ≡ pr (fst ar) (pr (# k) (fst a))
                → ⟨ fst ar ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
                  × ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
    valK : (k : ℕ) (c ar a b yc : S) → ⟨ fst c ∈ fst (lookup (suc (suc zero)) γ) ⟩
           → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
           → ⟨ pr (fst c) (fst yc) ∈ fst (lookup (suc zero) γ) ⟩
           → ⟨ fst yc ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
    valK-un : (k : ℕ) (c ar a yc : S) → ⟨ fst c ∈ fst (lookup (suc (suc zero)) γ) ⟩
              → fst c ≡ pr (fst ar) (pr (# k) (fst a))
              → ⟨ pr (fst c) (fst yc) ∈ fst (lookup (suc zero) γ) ⟩
              → ⟨ fst yc ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
    t0eq : fst (lookup (suc (suc (suc (suc (suc (suc t0)))))) γ) ≡ fst (numeralL 0)
    t1eq : fst (lookup (suc (suc (suc (suc (suc (suc t1)))))) γ) ≡ fst (numeralL 1)
    t0K : ⟨ fst (lookup (suc (suc (suc (suc (suc (suc t0)))))) γ)
            ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
    num1K : ⟨ fst (numeralL 1) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
    envK-mem : (yc b a ar c E : S) → ⟨ (E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
                 envSetAt zero (suc (suc (suc (suc zero))))
                           (suc (suc (suc (suc (suc (suc zero)))))) ⟩
              → ⟨ fst E ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
    envK-neg : (ya yc a ar c E : S) → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨
                 envSetAt zero (suc (suc (suc (suc zero))))
                           (suc (suc (suc (suc (suc (suc zero)))))) ⟩
              → ⟨ fst E ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
    envK-imp : (E yb ya yc b a ar c : S) → ⟨ (E ∷ yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
                 envSetAt zero (suc (suc (suc (suc (suc (suc zero))))))
                           (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) ⟩
              → ⟨ fst E ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
    envInK-mem : (yc b a ar c E z : S) → ⟨ (z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
                   envOverAt zero (suc (suc (suc (suc (suc zero)))))
                               (suc (suc (suc (suc (suc (suc (suc zero))))))) ⟩
                → ⟨ fst z ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
    envInK-neg : (ya yc a ar c E z : S) → ⟨ (z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨
                   envOverAt zero (suc (suc (suc (suc (suc zero)))))
                               (suc (suc (suc (suc (suc (suc (suc zero))))))) ⟩
                → ⟨ fst z ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
    envInK-imp : (E ya yc b a ar c z : S) → ⟨ (z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
                   envOverAt zero (suc (suc (suc (suc (suc (suc zero))))))
                               (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) ⟩
                → ⟨ fst z ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
    valV : (E yc b a ar c z v w : S) → ⟨ (w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
              tmValAt (suc (suc (suc (suc (suc (suc zero))))))
                      (suc (suc zero))
                      (suc zero) ⟩
            → ⟨ fst v ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc K)))))))))))))
                              (z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)) ⟩
    valW : (E yc b a ar c z v w : S) → ⟨ (w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
              tmValAt (suc (suc (suc (suc (suc zero)))))
                      (suc (suc zero))
                      zero ⟩
            → ⟨ fst w ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc K))))))))))))))
                              (v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)) ⟩
    transK : (x a : S) → ⟨ fst x ∈ fst a ⟩
             → ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
             → ⟨ fst x ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
    subK₁-and : (x y yc b a ar c : S) → ⟨ (x ∷ y ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
                  subValAt {7 + (11 + n)} (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
                           (suc (suc (suc (suc (suc zero)))))
                           (suc (suc (suc (suc zero))))
                           (suc zero) ⟩
                → ⟨ fst y ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
    subK₀-and : (y ya yc b a ar c : S) → ⟨ (y ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
                  subValAt {7 + (11 + n)} (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
                           (suc (suc (suc (suc (suc zero)))))
                           (suc (suc (suc zero)))
                           zero ⟩
                → ⟨ fst y ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
    subK₁-imp : (E yb ya yc b a ar c : S) → ⟨ (E ∷ yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
                  subValAt (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
                           (suc (suc (suc (suc (suc (suc zero))))))
                           (suc (suc (suc (suc (suc zero)))))
                           (suc (suc zero)) ⟩
                → ⟨ fst ya ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
    subK₀-imp : (E yb ya yc b a ar c : S) → ⟨ (E ∷ yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
                  subValAt (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
                           (suc (suc (suc (suc (suc (suc zero))))))
                           (suc (suc (suc (suc zero))))
                           (suc zero) ⟩
                → ⟨ fst yb ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
    someEnv : someEnvDef {n} K γ
    subK-neg : (ya yc a ar c E : S) → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨
                 subValAt (suc (suc (suc (suc (suc (suc (suc zero)))))))
                          (suc (suc (suc (suc zero))))
                          (suc (suc (suc zero)))
                          (suc zero) ⟩
               → ⟨ fst ya ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩

module LowerAgree {n : ℕ}
  (N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K : Fin (5 + n))
  (γ : S ^ (11 + n))
  (lf : LFacts N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K γ)
  where

  open LFacts lf

  -- The tied keyK-neg, derived once from pairK ([LJ-1.109]
  -- TiesSupplied): pr (fst ar) (fst a) is the hierarchy pair of the
  -- L-pair prʟ ar a, which pairK closes.  The Neg row's site binds
  -- arK and aK; this derivation is not a hypothesis (C-38).
  module KN = KeyNegTies {11 + n} (suc (suc (suc (suc (suc (suc K)))))) γ pairK

  keyK-neg-tied : (E ya yc a ar c : S)
                → ⟨ fst ar ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
                → ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
                → ⟨ pr (fst ar) (fst a)
                     ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
  keyK-neg-tied E ya yc a ar c arK aK = KN.key-neg-tied ar a arK aK

  -- The rows' arityK is the frame's transK with the binder roles
  -- swapped: transK x a closes x ∈ a, the row's arityK N v closes
  -- v ∈ N.  One derivation, reused at every application ([LJ-1.93]).
  arityK : (N v : S) → ⟨ fst v ∈ fst N ⟩
         → ⟨ fst N ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
         → ⟨ fst v ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
  arityK N v hv hNK = transK v N hv hNK

  module M = MemAgree {11 + n} (suc (suc zero)) (suc zero) zero
               (suc (suc (suc (suc (suc (suc N0)))))) (suc (suc (suc (suc (suc (suc K)))))) (suc (suc (suc (suc (suc (suc t0)))))) (suc (suc (suc (suc (suc (suc t1)))))) γ
               tagEq0 numK0
               (λ a b aK bK → innerK 0 (prʟ a b) (pairK a b aK bK)) (λ a b aK bK → pairK a b aK bK) arityK (codesK 0) (valK 0)
               t0eq t1eq t0K num1K envK-mem envInK-mem
               valV valW

  module E = EqAgree {11 + n} (suc (suc zero)) (suc zero) zero
               (suc (suc (suc (suc (suc (suc N1)))))) (suc (suc (suc (suc (suc (suc K)))))) (suc (suc (suc (suc (suc (suc t0)))))) (suc (suc (suc (suc (suc (suc t1)))))) γ
               tagEq1 numK1
               (λ a b aK bK → innerK 1 (prʟ a b) (pairK a b aK bK)) (λ a b aK bK → pairK a b aK bK) arityK (codesK 1) (valK 1)
               t0eq t1eq t0K num1K envK-mem envInK-mem
               valV valW

  module A = AndAgree {11 + n} (suc (suc zero)) (suc zero) zero
               (suc (suc (suc (suc (suc (suc N2)))))) (suc (suc (suc (suc (suc (suc K)))))) γ
               tagEq2 numK2
               (λ a b aK bK → innerK 2 (prʟ a b) (pairK a b aK bK)) (λ a b aK bK → pairK a b aK bK) (codesK 2) (valK 2)
               (λ x y xK yK → pairK x y xK yK) transK subK₁-and subK₀-and someEnv

  module O = OrAgree {11 + n} (suc (suc zero)) (suc zero) zero
               (suc (suc (suc (suc (suc (suc N3)))))) (suc (suc (suc (suc (suc (suc K)))))) γ
               tagEq3 numK3
               (λ a b aK bK → innerK 3 (prʟ a b) (pairK a b aK bK)) (λ a b aK bK → pairK a b aK bK) (codesK 3) (valK 3)
               (λ x y xK yK → pairK x y xK yK) transK subK₁-and subK₀-and someEnv

  module I = ImpAgree {11 + n} (suc (suc zero)) (suc zero) zero
               (suc (suc (suc (suc (suc (suc N4)))))) (suc (suc (suc (suc (suc (suc K)))))) γ
               tagEq4 numK4
               (λ a b aK bK → innerK 4 (prʟ a b) (pairK a b aK bK)) (λ a b aK bK → pairK a b aK bK) arityK (codesK 4) (valK 4)
               (λ x y xK yK → pairK x y xK yK) subK₁-imp subK₀-imp envK-imp envInK-imp

  module N = NegAgree {11 + n} (suc (suc zero)) (suc zero) zero
               (suc (suc (suc (suc (suc (suc N5)))))) (suc (suc (suc (suc (suc (suc K)))))) γ
               tagEq5 numK5
               (λ a aK → innerK 5 a aK) arityK (codesK-un 5) (valK-un 5)
               keyK-neg-tied subK-neg envK-neg envInK-neg

  sixB : Formula S (11 + n)
  sixB =
    Mem.memBndAt {11 + n} (suc (suc zero)) (suc zero) zero
      (suc (suc (suc (suc (suc (suc N0))))))
      (suc (suc (suc (suc (suc (suc K))))))
      (suc (suc (suc (suc (suc (suc t0))))))
      (suc (suc (suc (suc (suc (suc t1))))))
    ∧̇ (Eq.eqBndAt {11 + n} (suc (suc zero)) (suc zero) zero
      (suc (suc (suc (suc (suc (suc N1))))))
      (suc (suc (suc (suc (suc (suc K))))))
      (suc (suc (suc (suc (suc (suc t0))))))
      (suc (suc (suc (suc (suc (suc t1))))))
    ∧̇ (And.andBndAt {11 + n} (suc (suc zero)) (suc zero) zero
      (suc (suc (suc (suc (suc (suc N2))))))
      (suc (suc (suc (suc (suc (suc K))))))
    ∧̇ (Or.orBndAt {11 + n} (suc (suc zero)) (suc zero) zero
      (suc (suc (suc (suc (suc (suc N3))))))
      (suc (suc (suc (suc (suc (suc K))))))
    ∧̇ (Imp.impBndAt {11 + n} (suc (suc zero)) (suc zero) zero
      (suc (suc (suc (suc (suc (suc N4))))))
      (suc (suc (suc (suc (suc (suc K))))))
    ∧̇ (Neg.negBndAt {11 + n} (suc (suc zero)) (suc zero) zero
      (suc (suc (suc (suc (suc (suc N5))))))
      (suc (suc (suc (suc (suc (suc K))))))
    )))))

  sixAt : Formula S (11 + n)
  sixAt =
    memClauseAt {11 + n} (suc (suc zero)) (suc zero) zero
    ∧̇ (eqClauseAt {11 + n} (suc (suc zero)) (suc zero) zero
    ∧̇ (andClauseAt {11 + n} (suc (suc zero)) (suc zero)
    ∧̇ (orClauseAt {11 + n} (suc (suc zero)) (suc zero)
    ∧̇ (impClauseAt {11 + n} (suc (suc zero)) (suc zero) zero
    ∧̇ (negClauseAt {11 + n} (suc (suc zero)) (suc zero) zero
    )))))

  out : ⟨ γ ⊨ twelveAt (suc (suc zero)) (suc zero) zero ⟩ → ⟨ γ ⊨ sixB ⟩
  out h =
    ( M.out (h .fst)
    , ( E.out (h .snd .fst)
      , ( A.out (h .snd .snd .fst)
        , ( O.out (h .snd .snd .snd .fst)
          , ( I.out (h .snd .snd .snd .snd .fst)
            , N.out (h .snd .snd .snd .snd .snd .fst) )))))

  back : ⟨ γ ⊨ sixB ⟩ → ⟨ γ ⊨ sixAt ⟩
  back h =
    ( M.back (h .fst)
    , ( E.back (h .snd .fst)
      , ( A.back (h .snd .snd .fst)
        , ( O.back (h .snd .snd .snd .fst)
          , ( I.back (h .snd .snd .snd .snd .fst)
            , N.back (h .snd .snd .snd .snd .snd) )))))
```

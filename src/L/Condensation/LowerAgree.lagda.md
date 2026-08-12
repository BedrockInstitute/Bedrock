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
  using ( prʟ; envSetAt; envOverAt; tmValAt; subValAt
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

module LowerAgree {n : ℕ}
  (N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K : Fin (5 + n))
  (γ : S ^ (11 + n))
  (tagEq0 : fst (lookup (suc (suc (suc (suc (suc (suc N0)))))) γ) ≡ fst (numeralL 0))
  (tagEq1 : fst (lookup (suc (suc (suc (suc (suc (suc N1)))))) γ) ≡ fst (numeralL 1))
  (tagEq2 : fst (lookup (suc (suc (suc (suc (suc (suc N2)))))) γ) ≡ fst (numeralL 2))
  (tagEq3 : fst (lookup (suc (suc (suc (suc (suc (suc N3)))))) γ) ≡ fst (numeralL 3))
  (tagEq4 : fst (lookup (suc (suc (suc (suc (suc (suc N4)))))) γ) ≡ fst (numeralL 4))
  (tagEq5 : fst (lookup (suc (suc (suc (suc (suc (suc N5)))))) γ) ≡ fst (numeralL 5))
  (numK0 : ⟨ fst (numeralL 0) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (numK1 : ⟨ fst (numeralL 1) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (numK2 : ⟨ fst (numeralL 2) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (numK3 : ⟨ fst (numeralL 3) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (numK4 : ⟨ fst (numeralL 4) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (numK5 : ⟨ fst (numeralL 5) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (innerK : (k : ℕ) (p : S) → ⟨ fst p ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
             → ⟨ fst (prʟ (numeralL k) p) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (pairK : (a b : S) → ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
             → ⟨ fst b ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
             → ⟨ fst (prʟ a b) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (codesK : (k : ℕ) (c ar a b : S) → ⟨ fst c ∈ fst (lookup (suc (suc zero)) γ) ⟩
            → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
            → ⟨ fst ar ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
              × ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
              × ⟨ fst b ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (codesK-un : (k : ℕ) (c ar a : S) → ⟨ fst c ∈ fst (lookup (suc (suc zero)) γ) ⟩
               → fst c ≡ pr (fst ar) (pr (# k) (fst a))
               → ⟨ fst ar ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
                 × ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (valK : (k : ℕ) (c ar a b yc : S) → ⟨ fst c ∈ fst (lookup (suc (suc zero)) γ) ⟩
          → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
          → ⟨ fst yc ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (valK-un : (k : ℕ) (c ar a yc : S) → ⟨ fst c ∈ fst (lookup (suc (suc zero)) γ) ⟩
             → fst c ≡ pr (fst ar) (pr (# k) (fst a))
             → ⟨ fst yc ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (t0eq : fst (lookup (suc (suc (suc (suc (suc (suc t0)))))) γ) ≡ fst (numeralL 0))
  (t1eq : fst (lookup (suc (suc (suc (suc (suc (suc t1)))))) γ) ≡ fst (numeralL 1))
  (t0K : ⟨ fst (lookup (suc (suc (suc (suc (suc (suc t0)))))) γ)
           ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (tmKeyK : (k : S) → ⟨ fst k ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (num1K : ⟨ fst (numeralL 1) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (envK-mem : (yc b a ar c E : S) → ⟨ (E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
                envSetAt zero (suc (suc (suc (suc zero))))
                          (suc (suc (suc (suc (suc (suc zero)))))) ⟩
             → ⟨ fst E ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (envK-neg : (ya yc a ar c E : S) → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨
                envSetAt zero (suc (suc (suc (suc zero))))
                          (suc (suc (suc (suc (suc (suc zero)))))) ⟩
             → ⟨ fst E ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (envK-imp : (E yb ya yc b a ar c : S) → ⟨ (E ∷ yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
                envSetAt zero (suc (suc (suc (suc (suc (suc zero))))))
                          (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) ⟩
             → ⟨ fst E ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (entryK : (z x y : S) → ⟨ pr (fst x) (fst y) ∈ fst z ⟩
            → ⟨ fst x ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
              × ⟨ fst y ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (arSubK-mem : (yc b a ar c x : S) → ⟨ fst x ∈ fst (lookup (suc (suc (suc zero)))
                                          (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)) ⟩
                → ⟨ fst x ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (arSubK-neg : (ya yc a ar c x : S) → ⟨ fst x ∈ fst (lookup (suc (suc (suc zero)))
                                          (ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ)) ⟩
                → ⟨ fst x ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (arSubK-imp : (ya yc b a ar c x : S) → ⟨ fst x ∈ fst (lookup (suc (suc (suc (suc zero))))
                                          (ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)) ⟩
                → ⟨ fst x ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (envInK-mem : (yc b a ar c E z : S) → ⟨ (z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
                  envOverAt zero (suc (suc (suc (suc (suc zero)))))
                              (suc (suc (suc (suc (suc (suc (suc zero))))))) ⟩
               → ⟨ fst z ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (envInK-neg : (ya yc a ar c E z : S) → ⟨ (z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨
                  envOverAt zero (suc (suc (suc (suc (suc zero)))))
                              (suc (suc (suc (suc (suc (suc (suc zero))))))) ⟩
               → ⟨ fst z ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (envInK-imp : (E ya yc b a ar c z : S) → ⟨ (z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
                  envOverAt zero (suc (suc (suc (suc (suc (suc zero))))))
                              (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) ⟩
               → ⟨ fst z ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (valV : (E yc b a ar c z v w : S) → ⟨ (w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
             tmValAt (suc (suc (suc (suc (suc (suc zero))))))
                     (suc (suc zero))
                     (suc zero) ⟩
           → ⟨ fst v ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc K)))))))))))))
                             (z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)) ⟩)
  (valW : (E yc b a ar c z v w : S) → ⟨ (w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
             tmValAt (suc (suc (suc (suc (suc zero)))))
                     (suc (suc zero))
                     zero ⟩
           → ⟨ fst w ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc K))))))))))))))
                             (v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)) ⟩)
  (transK : (x a : S) → ⟨ fst x ∈ fst a ⟩
            → ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
            → ⟨ fst x ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (subK₁-and : (x y yc b a ar c : S) → ⟨ (x ∷ y ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
                 subValAt {7 + (11 + n)} (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
                          (suc (suc (suc (suc (suc zero)))))
                          (suc (suc (suc (suc zero))))
                          (suc zero) ⟩
               → ⟨ fst y ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (subK₀-and : (y ya yc b a ar c : S) → ⟨ (y ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
                 subValAt {7 + (11 + n)} (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
                          (suc (suc (suc (suc (suc zero)))))
                          (suc (suc (suc zero)))
                          zero ⟩
               → ⟨ fst y ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (subK₁-imp : (E yb ya yc b a ar c : S) → ⟨ (E ∷ yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
                 subValAt (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
                          (suc (suc (suc (suc (suc (suc zero))))))
                          (suc (suc (suc (suc (suc zero)))))
                          (suc (suc zero)) ⟩
               → ⟨ fst ya ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (subK₀-imp : (E yb ya yc b a ar c : S) → ⟨ (E ∷ yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
                 subValAt (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
                          (suc (suc (suc (suc (suc (suc zero))))))
                          (suc (suc (suc (suc zero))))
                          (suc zero) ⟩
               → ⟨ fst yb ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (someEnv : someEnvDef {n} K γ)
  (subK-neg : (ya yc a ar c E : S) → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨
                subValAt (suc (suc (suc (suc (suc (suc (suc zero)))))))
                         (suc (suc (suc (suc zero))))
                         (suc (suc (suc zero)))
                         (suc zero) ⟩
              → ⟨ fst ya ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (keyK-neg : (E ya yc a ar c : S) → ⟨
                pr (fst (lookup (suc (suc (suc (suc zero)))) (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ)))
                   (fst (lookup (suc (suc (suc zero))) (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ)))
                ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc K)))))))))))) (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ)) ⟩)
  where

  module M = MemAgree {11 + n} (suc (suc zero)) (suc zero) zero
               (suc (suc (suc (suc (suc (suc N0)))))) (suc (suc (suc (suc (suc (suc K)))))) (suc (suc (suc (suc (suc (suc t0)))))) (suc (suc (suc (suc (suc (suc t1)))))) γ
               tagEq0 numK0
               (λ a b aK bK → innerK 0 (prʟ a b) (pairK a b aK bK)) (λ a b aK bK → pairK a b aK bK) (codesK 0) (valK 0)
               t0eq t1eq t0K tmKeyK num1K envK-mem entryK arSubK-mem envInK-mem
               valV valW

  module E = EqAgree {11 + n} (suc (suc zero)) (suc zero) zero
               (suc (suc (suc (suc (suc (suc N1)))))) (suc (suc (suc (suc (suc (suc K)))))) (suc (suc (suc (suc (suc (suc t0)))))) (suc (suc (suc (suc (suc (suc t1)))))) γ
               tagEq1 numK1
               (λ a b aK bK → innerK 1 (prʟ a b) (pairK a b aK bK)) (λ a b aK bK → pairK a b aK bK) (codesK 1) (valK 1)
               t0eq t1eq t0K tmKeyK num1K envK-mem entryK arSubK-mem envInK-mem
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
               (λ a b aK bK → innerK 4 (prʟ a b) (pairK a b aK bK)) (λ a b aK bK → pairK a b aK bK) (codesK 4) (valK 4)
               (λ x y xK yK → pairK x y xK yK) subK₁-imp subK₀-imp envK-imp entryK arSubK-imp envInK-imp

  module N = NegAgree {11 + n} (suc (suc zero)) (suc zero) zero
               (suc (suc (suc (suc (suc (suc N5)))))) (suc (suc (suc (suc (suc (suc K)))))) γ
               tagEq5 numK5
               (λ a aK → innerK 5 a aK) (codesK-un 5) (valK-un 5)
               keyK-neg subK-neg envK-neg entryK arSubK-neg envInK-neg

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

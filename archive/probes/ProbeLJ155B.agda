{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.55] probe B: the twelve-row composition at the consumer's
-- frame.  After the slot generalization, each agreement instantiates
-- at the twelve frame (arity 11 + n) with C = 2, T = 1, B = 0,
-- N = suc^6 Ni, K = suc^6 K, t0/t1 = suc^6 t0/suc^6 t1.  The
-- per-row modules collect each row's site facts; TwelveAgree threads
-- the conjunction in both directions.
--
-- Untracked probe; never committed.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ155B {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

import FOL.Absoluteness
open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _∧̇_; _∈̇_ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Axioms.Numerals {ℓ} using ( numeralL )
open import L.Coding.Model {ℓ}
  using ( memClauseAt; eqClauseAt; andClauseAt; orClauseAt; impClauseAt
        ; negClauseAt; topClauseAt; botClauseAt; existClauseAt
        ; forallClauseAt; allInClauseAt; exInClauseAt
        ; tmValAt; envSetAt; envOverAt; subValAt; subValSuccAt
        ; consAtL; prʟ )
open import L.Coding.Graph {ℓ} lem using ( twelveAt )
open import L.Condensation {ℓ} lem using
  ( module Bot; module Top; module Neg; module Forall; module Exist
  ; module And; module Or; module Imp; module Mem; module Eq
  ; module AllIn; module ExIn
  ; module BotAgree; module TopAgree; module NegAgree
  ; module ForallAgree; module ExistAgree; module AndAgree
  ; module OrAgree; module ImpAgree; module MemAgree; module EqAgree
  ; module AllInAgree; module ExInAgree
  ; envHypB2; keyU; succU )

open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet using ( #_; sucV )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Foundations.Function using ( _∘_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- Depth-lift helpers for the twelve frame: suc^d (suc^6 K).
six : ∀ {n} → Fin n → Fin (6 + n)
six = λ i → suc (suc (suc (suc (suc (suc i)))))

seven : ∀ {n} → Fin n → Fin (7 + n)
seven = λ i → suc (suc (suc (suc (suc (suc (suc i))))))

eight : ∀ {n} → Fin n → Fin (8 + n)
eight = λ i → suc (suc (suc (suc (suc (suc (suc (suc i)))))))

ten : ∀ {n} → Fin n → Fin (10 + n)
ten = λ i → suc (suc (suc (suc (suc (suc (suc (suc (suc (suc i)))))))))


-- =====================================================================
-- THE TWELVE ROW INSTANTIATIONS AT THE TWELVE FRAME.
-- =====================================================================
module RowMem {n : ℕ} (N0 K t0 t1 : Fin (5 + n)) (γ : S ^ (11 + n))
  (tagEq : fst (lookup (suc (suc (suc (suc (suc (suc N0)))))) γ) ≡ fst (numeralL 0))
  (numK : ⟨ fst (numeralL 0) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (innerK : (a b : S) → ⟨ fst (prʟ (numeralL 0) (prʟ a b))
             ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (pairK : (a b : S) → ⟨ fst (prʟ a b) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (codesK : (c ar a b : S) → ⟨ fst c ∈ fst (lookup (suc (suc zero)) γ) ⟩
           → fst c ≡ pr (fst ar) (pr (# 0) (pr (fst a) (fst b)))
           → ⟨ fst ar ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
             × ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
             × ⟨ fst b ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (valK : (c ar a b yc : S) → ⟨ fst c ∈ fst (lookup (suc (suc zero)) γ) ⟩
         → fst c ≡ pr (fst ar) (pr (# 0) (pr (fst a) (fst b)))
         → ⟨ fst yc ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (t0eq : fst (lookup (suc (suc (suc (suc (suc (suc t0)))))) γ) ≡ fst (numeralL 0))
  (t1eq : fst (lookup (suc (suc (suc (suc (suc (suc t1)))))) γ) ≡ fst (numeralL 1))
  (t0K : ⟨ fst (lookup (suc (suc (suc (suc (suc (suc t0)))))) γ)
           ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (tmKeyK : (k : S) → ⟨ fst k ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (num1K : ⟨ fst (numeralL 1) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (envK : (yc b a ar c E : S) → ⟨ (E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
             envSetAt zero (suc (suc (suc (suc zero))))
                       (suc (suc (suc (suc (suc (suc zero))))) ) ⟩
         → ⟨ fst E ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (entryK : (z x y : S) → ⟨ pr (fst x) (fst y) ∈ fst z ⟩
           → ⟨ fst x ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
             × ⟨ fst y ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (arSubK : (yc b a ar c x : S) → ⟨ fst x ∈ fst (lookup (suc (suc (suc zero)))
                                       (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)) ⟩
           → ⟨ fst x ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (envInK : (yc b a ar c E z : S) → ⟨ (z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
               envOverAt zero (suc (suc (suc (suc (suc zero)))))
                          (suc (suc (suc (suc (suc (suc (suc zero))))))) ⟩
           → ⟨ fst z ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (valV : (E yc b a ar c z v w : S) → ⟨ (w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
             tmValAt (suc (suc (suc (suc (suc (suc zero))))))
                     (suc (suc zero))
                     (suc zero) ⟩
         → ⟨ fst v ∈ fst (lookup (seven (six K))
                           (z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)) ⟩)
  (valW : (E yc b a ar c z v w : S) → ⟨ (w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
             tmValAt (suc (suc (suc (suc (suc zero)))))
                     (suc (suc zero))
                     zero ⟩
         → ⟨ fst w ∈ fst (lookup (eight (six K))
                           (v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)) ⟩) where

  module A = MemAgree {11 + n} (suc (suc zero)) (suc zero) zero
               (suc (suc (suc (suc (suc (suc N0))))))
               (suc (suc (suc (suc (suc (suc K))))))
               (suc (suc (suc (suc (suc (suc t0))))))
               (suc (suc (suc (suc (suc (suc t1)))))) γ
               tagEq numK innerK pairK codesK valK t0eq t1eq t0K tmKeyK num1K
               envK entryK arSubK envInK valV valW

  row : Formula S (11 + n)
  row = Mem.memBndAt {11 + n} (suc (suc zero)) (suc zero) zero
          (suc (suc (suc (suc (suc (suc N0))))))
          (suc (suc (suc (suc (suc (suc K))))))
          (suc (suc (suc (suc (suc (suc t0))))))
          (suc (suc (suc (suc (suc (suc t1))))))

  out : ⟨ γ ⊨ memClauseAt (suc (suc zero)) (suc zero) zero ⟩ → ⟨ γ ⊨ row ⟩
  out = A.out

  back : ⟨ γ ⊨ row ⟩ → ⟨ γ ⊨ memClauseAt (suc (suc zero)) (suc zero) zero ⟩
  back = A.back

module RowEq {n : ℕ} (N1 K t0 t1 : Fin (5 + n)) (γ : S ^ (11 + n))
  (tagEq : fst (lookup (suc (suc (suc (suc (suc (suc N1)))))) γ) ≡ fst (numeralL 1))
  (numK : ⟨ fst (numeralL 1) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (innerK : (a b : S) → ⟨ fst (prʟ (numeralL 1) (prʟ a b))
             ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (pairK : (a b : S) → ⟨ fst (prʟ a b) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (codesK : (c ar a b : S) → ⟨ fst c ∈ fst (lookup (suc (suc zero)) γ) ⟩
           → fst c ≡ pr (fst ar) (pr (# 1) (pr (fst a) (fst b)))
           → ⟨ fst ar ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
             × ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
             × ⟨ fst b ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (valK : (c ar a b yc : S) → ⟨ fst c ∈ fst (lookup (suc (suc zero)) γ) ⟩
         → fst c ≡ pr (fst ar) (pr (# 1) (pr (fst a) (fst b)))
         → ⟨ fst yc ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (t0eq : fst (lookup (suc (suc (suc (suc (suc (suc t0)))))) γ) ≡ fst (numeralL 0))
  (t1eq : fst (lookup (suc (suc (suc (suc (suc (suc t1)))))) γ) ≡ fst (numeralL 1))
  (t0K : ⟨ fst (lookup (suc (suc (suc (suc (suc (suc t0)))))) γ)
           ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (tmKeyK : (k : S) → ⟨ fst k ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (num1K : ⟨ fst (numeralL 1) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (envK : (yc b a ar c E : S) → ⟨ (E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
             envSetAt zero (suc (suc (suc (suc zero))))
                       (suc (suc (suc (suc (suc (suc zero))))) ) ⟩
         → ⟨ fst E ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (entryK : (z x y : S) → ⟨ pr (fst x) (fst y) ∈ fst z ⟩
           → ⟨ fst x ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
             × ⟨ fst y ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (arSubK : (yc b a ar c x : S) → ⟨ fst x ∈ fst (lookup (suc (suc (suc zero)))
                                       (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)) ⟩
           → ⟨ fst x ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (envInK : (yc b a ar c E z : S) → ⟨ (z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
               envOverAt zero (suc (suc (suc (suc (suc zero)))))
                          (suc (suc (suc (suc (suc (suc (suc zero))))))) ⟩
           → ⟨ fst z ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (valV : (E yc b a ar c z v w : S) → ⟨ (w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
             tmValAt (suc (suc (suc (suc (suc (suc zero))))))
                     (suc (suc zero))
                     (suc zero) ⟩
         → ⟨ fst v ∈ fst (lookup (seven (six K))
                           (z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)) ⟩)
  (valW : (E yc b a ar c z v w : S) → ⟨ (w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
             tmValAt (suc (suc (suc (suc (suc zero)))))
                     (suc (suc zero))
                     zero ⟩
         → ⟨ fst w ∈ fst (lookup (eight (six K))
                           (v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)) ⟩) where

  module A = EqAgree {11 + n} (suc (suc zero)) (suc zero) zero
               (suc (suc (suc (suc (suc (suc N1))))))
               (suc (suc (suc (suc (suc (suc K))))))
               (suc (suc (suc (suc (suc (suc t0))))))
               (suc (suc (suc (suc (suc (suc t1)))))) γ
               tagEq numK innerK pairK codesK valK t0eq t1eq t0K tmKeyK num1K
               envK entryK arSubK envInK valV valW

  row : Formula S (11 + n)
  row = Eq.eqBndAt {11 + n} (suc (suc zero)) (suc zero) zero
          (suc (suc (suc (suc (suc (suc N1))))))
          (suc (suc (suc (suc (suc (suc K))))))
          (suc (suc (suc (suc (suc (suc t0))))))
          (suc (suc (suc (suc (suc (suc t1))))))

  out : ⟨ γ ⊨ eqClauseAt (suc (suc zero)) (suc zero) zero ⟩ → ⟨ γ ⊨ row ⟩
  out = A.out

  back : ⟨ γ ⊨ row ⟩ → ⟨ γ ⊨ eqClauseAt (suc (suc zero)) (suc zero) zero ⟩
  back = A.back

module RowAnd {n : ℕ} (N2 K : Fin (5 + n)) (γ : S ^ (11 + n))
  (tagEq : fst (lookup (suc (suc (suc (suc (suc (suc N2)))))) γ) ≡ fst (numeralL 2))
  (numK : ⟨ fst (numeralL 2) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (innerK : (a b : S) → ⟨ fst (prʟ (numeralL 2) (prʟ a b))
             ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (pairK : (a b : S) → ⟨ fst (prʟ a b) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (codesK : (c ar a b : S) → ⟨ fst c ∈ fst (lookup (suc (suc zero)) γ) ⟩
           → fst c ≡ pr (fst ar) (pr (# 2) (pr (fst a) (fst b)))
           → ⟨ fst ar ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
             × ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
             × ⟨ fst b ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (valK : (c ar a b yc : S) → ⟨ fst c ∈ fst (lookup (suc (suc zero)) γ) ⟩
         → fst c ≡ pr (fst ar) (pr (# 2) (pr (fst a) (fst b)))
         → ⟨ fst yc ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (keyK : (ar a : S) → ⟨ fst (prʟ ar a) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (transK : (x a : S) → ⟨ fst x ∈ fst a ⟩
           → ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
           → ⟨ fst x ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (subK₁ : (x y yc b a ar c : S)
           → ⟨ (x ∷ y ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
                subValAt {7 + (11 + n)}
                  (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
                  (suc (suc (suc (suc (suc zero)))))
                  (suc (suc (suc (suc zero))))
                  (suc zero) ⟩ → ⟨ fst y ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (subK₀ : (y ya yc b a ar c : S)
           → ⟨ (y ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
                subValAt {7 + (11 + n)}
                  (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
                  (suc (suc (suc (suc (suc zero)))))
                  (suc (suc (suc zero)))
                  zero ⟩ → ⟨ fst y ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (someEnv : (ya yc b a ar c : S) → ⟨ fst ya ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
           → ⟨ fst yc ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
           → ⟨ fst ar ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
           → Σ S (λ E → ⟨ fst E ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
             × ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
                  envHypB2 {11 + n} zero (suc (suc (suc (suc (suc (suc K)))))) ⟩)) where

  module A = AndAgree {11 + n} (suc (suc zero)) (suc zero) zero
               (suc (suc (suc (suc (suc (suc N2))))))
               (suc (suc (suc (suc (suc (suc K)))))) γ
               tagEq numK innerK pairK codesK valK keyK transK subK₁ subK₀ someEnv

  row : Formula S (11 + n)
  row = And.andBndAt {11 + n} (suc (suc zero)) (suc zero) zero
          (suc (suc (suc (suc (suc (suc N2))))))
          (suc (suc (suc (suc (suc (suc K))))))

  out : ⟨ γ ⊨ andClauseAt (suc (suc zero)) (suc zero) ⟩ → ⟨ γ ⊨ row ⟩
  out = A.out

  back : ⟨ γ ⊨ row ⟩ → ⟨ γ ⊨ andClauseAt (suc (suc zero)) (suc zero) ⟩
  back = A.back

module RowOr {n : ℕ} (N3 K : Fin (5 + n)) (γ : S ^ (11 + n))
  (tagEq : fst (lookup (suc (suc (suc (suc (suc (suc N3)))))) γ) ≡ fst (numeralL 3))
  (numK : ⟨ fst (numeralL 3) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (innerK : (a b : S) → ⟨ fst (prʟ (numeralL 3) (prʟ a b))
             ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (pairK : (a b : S) → ⟨ fst (prʟ a b) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (codesK : (c ar a b : S) → ⟨ fst c ∈ fst (lookup (suc (suc zero)) γ) ⟩
           → fst c ≡ pr (fst ar) (pr (# 3) (pr (fst a) (fst b)))
           → ⟨ fst ar ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
             × ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
             × ⟨ fst b ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (valK : (c ar a b yc : S) → ⟨ fst c ∈ fst (lookup (suc (suc zero)) γ) ⟩
         → fst c ≡ pr (fst ar) (pr (# 3) (pr (fst a) (fst b)))
         → ⟨ fst yc ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (keyK : (ar a : S) → ⟨ fst (prʟ ar a) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (transK : (x a : S) → ⟨ fst x ∈ fst a ⟩
           → ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
           → ⟨ fst x ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (subK₁ : (x y yc b a ar c : S)
           → ⟨ (x ∷ y ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
                subValAt {7 + (11 + n)}
                  (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
                  (suc (suc (suc (suc (suc zero)))))
                  (suc (suc (suc (suc zero))))
                  (suc zero) ⟩ → ⟨ fst y ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (subK₀ : (y ya yc b a ar c : S)
           → ⟨ (y ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
                subValAt {7 + (11 + n)}
                  (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
                  (suc (suc (suc (suc (suc zero)))))
                  (suc (suc (suc zero)))
                  zero ⟩ → ⟨ fst y ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (someEnv : (ya yc b a ar c : S) → ⟨ fst ya ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
           → ⟨ fst yc ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
           → ⟨ fst ar ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
           → Σ S (λ E → ⟨ fst E ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
             × ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
                  envHypB2 {11 + n} zero (suc (suc (suc (suc (suc (suc K)))))) ⟩)) where

  module A = OrAgree {11 + n} (suc (suc zero)) (suc zero) zero
               (suc (suc (suc (suc (suc (suc N3))))))
               (suc (suc (suc (suc (suc (suc K)))))) γ
               tagEq numK innerK pairK codesK valK keyK transK subK₁ subK₀ someEnv

  row : Formula S (11 + n)
  row = Or.orBndAt {11 + n} (suc (suc zero)) (suc zero) zero
          (suc (suc (suc (suc (suc (suc N3))))))
          (suc (suc (suc (suc (suc (suc K))))))

  out : ⟨ γ ⊨ orClauseAt (suc (suc zero)) (suc zero) ⟩ → ⟨ γ ⊨ row ⟩
  out = A.out

  back : ⟨ γ ⊨ row ⟩ → ⟨ γ ⊨ orClauseAt (suc (suc zero)) (suc zero) ⟩
  back = A.back

module RowImp {n : ℕ} (N4 K : Fin (5 + n)) (γ : S ^ (11 + n))
  (tagEq : fst (lookup (suc (suc (suc (suc (suc (suc N4)))))) γ) ≡ fst (numeralL 4))
  (numK : ⟨ fst (numeralL 4) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (innerK : (a b : S) → ⟨ fst (prʟ (numeralL 4) (prʟ a b))
             ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (pairK : (a b : S) → ⟨ fst (prʟ a b) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (codesK : (c ar a b : S) → ⟨ fst c ∈ fst (lookup (suc (suc zero)) γ) ⟩
           → fst c ≡ pr (fst ar) (pr (# 4) (pr (fst a) (fst b)))
           → ⟨ fst ar ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
             × ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
             × ⟨ fst b ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (valK : (c ar a b yc : S) → ⟨ fst c ∈ fst (lookup (suc (suc zero)) γ) ⟩
         → fst c ≡ pr (fst ar) (pr (# 4) (pr (fst a) (fst b)))
         → ⟨ fst yc ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (keyK : (x y : S) → ⟨ fst (prʟ x y) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (subK₁ : (E yb ya yc b a ar c : S) → ⟨ (E ∷ yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
              subValAt (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
                       (suc (suc (suc (suc (suc (suc zero))))))
                       (suc (suc (suc (suc (suc zero)))))
                       (suc (suc zero)) ⟩ → ⟨ fst ya ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (subK₀ : (E yb ya yc b a ar c : S) → ⟨ (E ∷ yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
              subValAt (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
                       (suc (suc (suc (suc (suc (suc zero))))))
                       (suc (suc (suc (suc zero))))
                       (suc zero) ⟩ → ⟨ fst yb ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (envK : (E yb ya yc b a ar c : S) → ⟨ (E ∷ yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
             envSetAt zero (suc (suc (suc (suc (suc (suc zero))))))
                       (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) ⟩
         → ⟨ fst E ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (entryK : (z x y : S) → ⟨ pr (fst x) (fst y) ∈ fst z ⟩
           → ⟨ fst x ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
             × ⟨ fst y ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (arSubK : (ya yc b a ar c x : S) → ⟨ fst x ∈ fst (lookup (suc (suc (suc (suc zero))))
                                        (ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)) ⟩
           → ⟨ fst x ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (envInK : (E ya yc b a ar c z : S) → ⟨ (z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
               envOverAt zero (suc (suc (suc (suc (suc (suc zero))))))
                          (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) ⟩
           → ⟨ fst z ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩) where

  module A = ImpAgree {11 + n} (suc (suc zero)) (suc zero) zero
               (suc (suc (suc (suc (suc (suc N4))))))
               (suc (suc (suc (suc (suc (suc K)))))) γ
               tagEq numK innerK pairK codesK valK keyK subK₁ subK₀ envK entryK arSubK envInK

  row : Formula S (11 + n)
  row = Imp.impBndAt {11 + n} (suc (suc zero)) (suc zero) zero
          (suc (suc (suc (suc (suc (suc N4))))))
          (suc (suc (suc (suc (suc (suc K))))))

  out : ⟨ γ ⊨ impClauseAt (suc (suc zero)) (suc zero) zero ⟩ → ⟨ γ ⊨ row ⟩
  out = A.out

  back : ⟨ γ ⊨ row ⟩ → ⟨ γ ⊨ impClauseAt (suc (suc zero)) (suc zero) zero ⟩
  back = A.back

module RowNeg {n : ℕ} (N5 K : Fin (5 + n)) (γ : S ^ (11 + n))
  (tagEq : fst (lookup (suc (suc (suc (suc (suc (suc N5)))))) γ) ≡ fst (numeralL 5))
  (numK : ⟨ fst (numeralL 5) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (innerK : (a : S) → ⟨ fst (prʟ (numeralL 5) a)
             ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (codesK : (c ar a : S) → ⟨ fst c ∈ fst (lookup (suc (suc zero)) γ) ⟩
           → fst c ≡ pr (fst ar) (pr (# 5) (fst a))
           → ⟨ fst ar ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
             × ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (valK : (c ar a yc : S) → ⟨ fst c ∈ fst (lookup (suc (suc zero)) γ) ⟩
         → fst c ≡ pr (fst ar) (pr (# 5) (fst a))
         → ⟨ fst yc ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (keyK : (E ya yc a ar c : S) → ⟨
             pr (fst (lookup (suc (suc (suc (suc zero)))) (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ)))
                (fst (lookup (suc (suc (suc zero))) (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ)))
             ∈ fst (lookup (six (six K))
                      (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ)) ⟩)
  (subK : (ya yc a ar c E : S) → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨
             subValAt (suc (suc (suc (suc (suc (suc (suc zero)))))))
                      (suc (suc (suc (suc zero))))
                      (suc (suc (suc zero)))
                      (suc zero) ⟩ → ⟨ fst ya ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (envK : (ya yc a ar c E : S) → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨
             envSetAt zero (suc (suc (suc (suc zero))))
                       (suc (suc (suc (suc (suc (suc zero)))))) ⟩
         → ⟨ fst E ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (entryK : (z x y : S) → ⟨ pr (fst x) (fst y) ∈ fst z ⟩
           → ⟨ fst x ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
             × ⟨ fst y ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (arSubK : (ya yc a ar c x : S) → ⟨ fst x ∈ fst (lookup (suc (suc (suc zero)))
                                       (ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ)) ⟩
           → ⟨ fst x ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (envInK : (ya yc a ar c E z : S) → ⟨ (z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨
               envOverAt zero (suc (suc (suc (suc (suc zero)))))
                          (suc (suc (suc (suc (suc (suc (suc zero))))))) ⟩
           → ⟨ fst z ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩) where

  module A = NegAgree {11 + n} (suc (suc zero)) (suc zero) zero
               (suc (suc (suc (suc (suc (suc N5))))))
               (suc (suc (suc (suc (suc (suc K)))))) γ
               tagEq numK innerK codesK valK keyK subK envK entryK arSubK envInK

  row : Formula S (11 + n)
  row = Neg.negBndAt {11 + n} (suc (suc zero)) (suc zero) zero
          (suc (suc (suc (suc (suc (suc N5))))))
          (suc (suc (suc (suc (suc (suc K))))))

  out : ⟨ γ ⊨ negClauseAt (suc (suc zero)) (suc zero) zero ⟩ → ⟨ γ ⊨ row ⟩
  out = A.out

  back : ⟨ γ ⊨ row ⟩ → ⟨ γ ⊨ negClauseAt (suc (suc zero)) (suc zero) zero ⟩
  back = A.back

module RowTop {n : ℕ} (N6 K : Fin (5 + n)) (γ : S ^ (11 + n))
  (tagEq : fst (lookup (suc (suc (suc (suc (suc (suc N6)))))) γ) ≡ fst (numeralL 6))
  (numK : ⟨ fst (numeralL 6) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (innerK : (a : S) → ⟨ fst (prʟ (numeralL 6) a)
             ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (codesK : (c ar a : S) → ⟨ fst c ∈ fst (lookup (suc (suc zero)) γ) ⟩
           → fst c ≡ pr (fst ar) (pr (# 6) (fst a))
           → ⟨ fst ar ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
             × ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (valK : (c ar a yc : S) → ⟨ fst c ∈ fst (lookup (suc (suc zero)) γ) ⟩
         → fst c ≡ pr (fst ar) (pr (# 6) (fst a))
         → ⟨ fst yc ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (envK : (yc a ar c E : S) → ⟨ (E ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨
             envSetAt zero (suc (suc (suc zero)))
                       (suc (suc (suc (suc (suc zero))))) ⟩
         → ⟨ fst E ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (entryK : (z x y : S) → ⟨ pr (fst x) (fst y) ∈ fst z ⟩
           → ⟨ fst x ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
             × ⟨ fst y ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (arSubK : (yc a ar c x : S) → ⟨ fst x ∈ fst (lookup (suc (suc zero)) (yc ∷ a ∷ ar ∷ c ∷ γ)) ⟩
           → ⟨ fst x ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (envInK : (yc a ar c E z : S) → ⟨ (z ∷ E ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨
               envOverAt zero (suc (suc (suc (suc zero))))
                          (suc (suc (suc (suc (suc (suc zero)))))) ⟩
           → ⟨ fst z ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩) where

  module A = TopAgree {11 + n} (suc (suc zero)) (suc zero) zero
               (suc (suc (suc (suc (suc (suc N6))))))
               (suc (suc (suc (suc (suc (suc K)))))) γ
               tagEq numK innerK codesK valK envK entryK arSubK envInK

  row : Formula S (11 + n)
  row = Top.topBndAt {11 + n} (suc (suc zero)) (suc zero) zero
          (suc (suc (suc (suc (suc (suc N6))))))
          (suc (suc (suc (suc (suc (suc K))))))

  out : ⟨ γ ⊨ topClauseAt (suc (suc zero)) (suc zero) zero ⟩ → ⟨ γ ⊨ row ⟩
  out = A.out

  back : ⟨ γ ⊨ row ⟩ → ⟨ γ ⊨ topClauseAt (suc (suc zero)) (suc zero) zero ⟩
  back = A.back

module RowBot {n : ℕ} (N7 K : Fin (5 + n)) (γ : S ^ (11 + n))
  (tagEq : fst (lookup (suc (suc (suc (suc (suc (suc N7)))))) γ) ≡ fst (numeralL 7))
  (numK : ⟨ fst (numeralL 7) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (innerK : (a : S) → ⟨ fst (prʟ (numeralL 7) a)
             ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (codesK : (c ar a : S) → ⟨ fst c ∈ fst (lookup (suc (suc zero)) γ) ⟩
           → fst c ≡ pr (fst ar) (pr (# 7) (fst a))
           → ⟨ fst ar ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
             × ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (valK : (c ar a yc : S) → ⟨ fst c ∈ fst (lookup (suc (suc zero)) γ) ⟩
         → fst c ≡ pr (fst ar) (pr (# 7) (fst a))
         → ⟨ fst yc ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩) where

  module A = BotAgree {11 + n} (suc (suc zero)) (suc zero) zero
               (suc (suc (suc (suc (suc (suc N7))))))
               (suc (suc (suc (suc (suc (suc K)))))) γ
               tagEq numK innerK codesK valK

  row : Formula S (11 + n)
  row = Bot.botBndAt {11 + n} (suc (suc zero)) (suc zero) zero
          (suc (suc (suc (suc (suc (suc N7))))))
          (suc (suc (suc (suc (suc (suc K))))))

  out : ⟨ γ ⊨ botClauseAt (suc (suc zero)) (suc zero) ⟩ → ⟨ γ ⊨ row ⟩
  out = A.bot-out

  back : ⟨ γ ⊨ row ⟩ → ⟨ γ ⊨ botClauseAt (suc (suc zero)) (suc zero) ⟩
  back = A.bot-in

module RowForall {n : ℕ} (N9 K : Fin (5 + n)) (γ : S ^ (11 + n))
  (tagEq : fst (lookup (suc (suc (suc (suc (suc (suc N9)))))) γ) ≡ fst (numeralL 9))
  (numK : ⟨ fst (numeralL 9) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (innerK : (a : S) → ⟨ fst (prʟ (numeralL 9) a)
             ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (codesK : (c ar a : S) → ⟨ fst c ∈ fst (lookup (suc (suc zero)) γ) ⟩
           → fst c ≡ pr (fst ar) (pr (# 9) (fst a))
           → ⟨ fst ar ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
             × ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (valK : (c ar a yc : S) → ⟨ fst c ∈ fst (lookup (suc (suc zero)) γ) ⟩
         → fst c ≡ pr (fst ar) (pr (# 9) (fst a))
         → ⟨ fst yc ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (succK : (E ya yc a ar c : S) →
             succU {11 + n} (suc (suc zero)) (suc zero) zero
               (suc (suc (suc (suc (suc (suc N9))))))
               (suc (suc (suc (suc (suc (suc K)))))) γ E ya yc a ar c)
  (keyK : (E ya yc a ar c : S) →
             keyU {11 + n} (suc (suc zero)) (suc zero) zero
               (suc (suc (suc (suc (suc (suc N9))))))
               (suc (suc (suc (suc (suc (suc K)))))) γ E ya yc a ar c)
  (subK : (ya yc a ar c E : S) → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨
             subValSuccAt (suc (suc (suc (suc (suc (suc (suc zero)))))))
                          (suc (suc (suc (suc zero))))
                          (suc (suc (suc zero)))
                          (suc zero) ⟩ → ⟨ fst ya ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (envK : (ya yc a ar c E : S) → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨
             envSetAt zero (suc (suc (suc (suc zero))))
                       (suc (suc (suc (suc (suc (suc zero)))))) ⟩
         → ⟨ fst E ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (entryK : (z x y : S) → ⟨ pr (fst x) (fst y) ∈ fst z ⟩
           → ⟨ fst x ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
             × ⟨ fst y ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (arSubK : (ya yc a ar c x : S) → ⟨ fst x ∈ fst (lookup (suc (suc (suc zero)))
                                       (ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ)) ⟩
           → ⟨ fst x ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (envInK : (ya yc a ar c E z : S) → ⟨ (z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨
               envOverAt zero (suc (suc (suc (suc (suc zero)))))
                          (suc (suc (suc (suc (suc (suc (suc zero))))))) ⟩
           → ⟨ fst z ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (consK : (ya yc a ar c E z x e' : S) → ⟨ (e' ∷ x ∷ z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨
               consAtL zero (suc zero) (suc (suc zero)) ⟩
          → ⟨ fst e' ∈ fst (lookup (eight (six K))
               (x ∷ z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ)) ⟩) where

  module A = ForallAgree {11 + n} (suc (suc zero)) (suc zero) zero
               (suc (suc (suc (suc (suc (suc N9))))))
               (suc (suc (suc (suc (suc (suc K)))))) γ
               tagEq numK innerK codesK valK succK keyK subK envK entryK arSubK envInK consK

  row : Formula S (11 + n)
  row = Forall.forallBndAt {11 + n} (suc (suc zero)) (suc zero) zero
          (suc (suc (suc (suc (suc (suc N9))))))
          (suc (suc (suc (suc (suc (suc K))))))

  out : ⟨ γ ⊨ forallClauseAt (suc (suc zero)) (suc zero) zero ⟩ → ⟨ γ ⊨ row ⟩
  out = A.out

  back : ⟨ γ ⊨ row ⟩ → ⟨ γ ⊨ forallClauseAt (suc (suc zero)) (suc zero) zero ⟩
  back = A.back

module RowExist {n : ℕ} (N8 K : Fin (5 + n)) (γ : S ^ (11 + n))
  (tagEq : fst (lookup (suc (suc (suc (suc (suc (suc N8)))))) γ) ≡ fst (numeralL 8))
  (numK : ⟨ fst (numeralL 8) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (innerK : (a : S) → ⟨ fst (prʟ (numeralL 8) a)
             ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (codesK : (c ar a : S) → ⟨ fst c ∈ fst (lookup (suc (suc zero)) γ) ⟩
           → fst c ≡ pr (fst ar) (pr (# 8) (fst a))
           → ⟨ fst ar ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
             × ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (valK : (c ar a yc : S) → ⟨ fst c ∈ fst (lookup (suc (suc zero)) γ) ⟩
         → fst c ≡ pr (fst ar) (pr (# 8) (fst a))
         → ⟨ fst yc ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (succK : (E ya yc a ar c : S) →
             succU {11 + n} (suc (suc zero)) (suc zero) zero
               (suc (suc (suc (suc (suc (suc N8))))))
               (suc (suc (suc (suc (suc (suc K)))))) γ E ya yc a ar c)
  (keyK : (E ya yc a ar c : S) →
             keyU {11 + n} (suc (suc zero)) (suc zero) zero
               (suc (suc (suc (suc (suc (suc N8))))))
               (suc (suc (suc (suc (suc (suc K)))))) γ E ya yc a ar c)
  (subK : (ya yc a ar c E : S) → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨
             subValSuccAt (suc (suc (suc (suc (suc (suc (suc zero)))))))
                          (suc (suc (suc (suc zero))))
                          (suc (suc (suc zero)))
                          (suc zero) ⟩ → ⟨ fst ya ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (envK : (ya yc a ar c E : S) → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨
             envSetAt zero (suc (suc (suc (suc zero))))
                       (suc (suc (suc (suc (suc (suc zero)))))) ⟩
         → ⟨ fst E ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (entryK : (z x y : S) → ⟨ pr (fst x) (fst y) ∈ fst z ⟩
           → ⟨ fst x ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
             × ⟨ fst y ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (arSubK : (ya yc a ar c x : S) → ⟨ fst x ∈ fst (lookup (suc (suc (suc zero)))
                                       (ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ)) ⟩
           → ⟨ fst x ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (envInK : (ya yc a ar c E z : S) → ⟨ (z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨
               envOverAt zero (suc (suc (suc (suc (suc zero)))))
                          (suc (suc (suc (suc (suc (suc (suc zero))))))) ⟩
           → ⟨ fst z ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (consK : (ya yc a ar c E z x e' : S) → ⟨ (e' ∷ x ∷ z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨
               consAtL zero (suc zero) (suc (suc zero))
               ∧̇ (var zero ∈̇ var (suc (suc (suc (suc zero))))) ⟩
          → ⟨ fst e' ∈ fst (lookup (eight (six K))
               (x ∷ z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ)) ⟩) where

  module A = ExistAgree {11 + n} (suc (suc zero)) (suc zero) zero
               (suc (suc (suc (suc (suc (suc N8))))))
               (suc (suc (suc (suc (suc (suc K)))))) γ
               tagEq numK innerK codesK valK succK keyK subK envK entryK arSubK envInK consK

  row : Formula S (11 + n)
  row = Exist.existBndAt {11 + n} (suc (suc zero)) (suc zero) zero
          (suc (suc (suc (suc (suc (suc N8))))))
          (suc (suc (suc (suc (suc (suc K))))))

  out : ⟨ γ ⊨ existClauseAt (suc (suc zero)) (suc zero) zero ⟩ → ⟨ γ ⊨ row ⟩
  out = A.out

  back : ⟨ γ ⊨ row ⟩ → ⟨ γ ⊨ existClauseAt (suc (suc zero)) (suc zero) zero ⟩
  back = A.back

module RowAllIn {n : ℕ} (N10 K t0 t1 : Fin (5 + n)) (γ : S ^ (11 + n))
  (tagEq : fst (lookup (suc (suc (suc (suc (suc (suc N10)))))) γ) ≡ fst (numeralL 10))
  (numK : ⟨ fst (numeralL 10) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (innerK : (a b : S) → ⟨ fst (prʟ (numeralL 10) (prʟ a b))
             ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (pairK : (a b : S) → ⟨ fst (prʟ a b) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (codesK : (c ar a b : S) → ⟨ fst c ∈ fst (lookup (suc (suc zero)) γ) ⟩
           → fst c ≡ pr (fst ar) (pr (# 10) (pr (fst a) (fst b)))
           → ⟨ fst ar ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
             × ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
             × ⟨ fst b ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (valK : (c ar a b yc : S) → ⟨ fst c ∈ fst (lookup (suc (suc zero)) γ) ⟩
         → fst c ≡ pr (fst ar) (pr (# 10) (pr (fst a) (fst b)))
         → ⟨ fst yc ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (succK : (E ya yc b a ar c : S) → ⟨
             sucV (fst (lookup (suc (suc (suc (suc (suc zero)))))
                        (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)))
             ∈ fst (lookup (seven (six K))
                       (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)) ⟩)
  (keyK : (E ya yc b a ar c : S) → ⟨
             pr (sucV (fst (lookup (suc (suc (suc (suc (suc zero)))))
                            (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ))))
                (fst (lookup (suc (suc (suc zero)))
                        (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)))
             ∈ fst (lookup (seven (six K))
                       (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)) ⟩)
  (subK : (E ya yc b a ar c : S) → ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
             subValSuccAt (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
                          (suc (suc (suc (suc (suc zero)))))
                          (suc (suc (suc zero)))
                          (suc zero) ⟩ → ⟨ fst ya ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (envK : (E ya yc b a ar c : S) → ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
             envSetAt zero (suc (suc (suc (suc (suc zero)))))
                       (suc (suc (suc (suc (suc (suc (suc zero))))))) ⟩
         → ⟨ fst E ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (entryK : (z x y : S) → ⟨ pr (fst x) (fst y) ∈ fst z ⟩
           → ⟨ fst x ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
             × ⟨ fst y ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (arSubK : (ya yc b a ar c x : S) → ⟨ fst x ∈ fst (lookup (suc (suc (suc (suc zero))))
                                        (ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)) ⟩
           → ⟨ fst x ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (envInK : (E ya yc b a ar c z : S) → ⟨ (z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
               envOverAt zero (suc (suc (suc (suc (suc (suc zero))))))
                           (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) ⟩
           → ⟨ fst z ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (t0eq : fst (lookup (suc (suc (suc (suc (suc (suc t0)))))) γ) ≡ fst (numeralL 0))
  (t1eq : fst (lookup (suc (suc (suc (suc (suc (suc t1)))))) γ) ≡ fst (numeralL 1))
  (t0K : ⟨ fst (lookup (suc (suc (suc (suc (suc (suc t0)))))) γ)
           ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (tmKeyK : (k : S) → ⟨ fst k ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (num1K : ⟨ fst (numeralL 1) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (wKfact : (E ya yc b a ar c z w : S) → ⟨ (w ∷ z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
              tmValAt (suc (suc (suc (suc (suc (suc zero))))))
                      (suc zero)
                      zero ⟩
          → ⟨ fst w ∈ fst (lookup (eight (six K))
               (z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)) ⟩)
  (consK : (E ya yc b a ar c z w x e' : S) → ⟨ (e' ∷ x ∷ w ∷ z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
               consAtL zero (suc zero) (suc (suc (suc zero))) ⟩
          → ⟨ fst e' ∈ fst (lookup (ten (six K))
               (x ∷ w ∷ z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)) ⟩) where

  module A = AllInAgree {11 + n} (suc (suc zero)) (suc zero) zero
               (suc (suc (suc (suc (suc (suc N10))))))
               (suc (suc (suc (suc (suc (suc K))))))
               (suc (suc (suc (suc (suc (suc t0))))))
               (suc (suc (suc (suc (suc (suc t1)))))) γ
               tagEq numK innerK pairK codesK valK succK keyK subK envK entryK
               arSubK envInK t0eq t1eq t0K tmKeyK num1K wKfact consK

  row : Formula S (11 + n)
  row = AllIn.allInBndAt {11 + n} (suc (suc zero)) (suc zero) zero
          (suc (suc (suc (suc (suc (suc N10))))))
          (suc (suc (suc (suc (suc (suc K))))))
          (suc (suc (suc (suc (suc (suc t0))))))
          (suc (suc (suc (suc (suc (suc t1))))))

  out : ⟨ γ ⊨ allInClauseAt (suc (suc zero)) (suc zero) zero ⟩ → ⟨ γ ⊨ row ⟩
  out = A.out

  back : ⟨ γ ⊨ row ⟩ → ⟨ γ ⊨ allInClauseAt (suc (suc zero)) (suc zero) zero ⟩
  back = A.back

module RowExIn {n : ℕ} (N11 K t0 t1 : Fin (5 + n)) (γ : S ^ (11 + n))
  (tagEq : fst (lookup (suc (suc (suc (suc (suc (suc N11)))))) γ) ≡ fst (numeralL 11))
  (numK : ⟨ fst (numeralL 11) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (innerK : (a b : S) → ⟨ fst (prʟ (numeralL 11) (prʟ a b))
             ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (pairK : (a b : S) → ⟨ fst (prʟ a b) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (codesK : (c ar a b : S) → ⟨ fst c ∈ fst (lookup (suc (suc zero)) γ) ⟩
           → fst c ≡ pr (fst ar) (pr (# 11) (pr (fst a) (fst b)))
           → ⟨ fst ar ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
             × ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
             × ⟨ fst b ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (valK : (c ar a b yc : S) → ⟨ fst c ∈ fst (lookup (suc (suc zero)) γ) ⟩
         → fst c ≡ pr (fst ar) (pr (# 11) (pr (fst a) (fst b)))
         → ⟨ fst yc ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (succK : (E ya yc b a ar c : S) → ⟨
             sucV (fst (lookup (suc (suc (suc (suc (suc zero)))))
                        (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)))
             ∈ fst (lookup (seven (six K))
                       (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)) ⟩)
  (keyK : (E ya yc b a ar c : S) → ⟨
             pr (sucV (fst (lookup (suc (suc (suc (suc (suc zero)))))
                            (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ))))
                (fst (lookup (suc (suc (suc zero)))
                        (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)))
             ∈ fst (lookup (seven (six K))
                       (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)) ⟩)
  (subK : (E ya yc b a ar c : S) → ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
             subValSuccAt (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
                          (suc (suc (suc (suc (suc zero)))))
                          (suc (suc (suc zero)))
                          (suc zero) ⟩ → ⟨ fst ya ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (envK : (E ya yc b a ar c : S) → ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
             envSetAt zero (suc (suc (suc (suc (suc zero)))))
                       (suc (suc (suc (suc (suc (suc (suc zero))))))) ⟩
         → ⟨ fst E ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (entryK : (z x y : S) → ⟨ pr (fst x) (fst y) ∈ fst z ⟩
           → ⟨ fst x ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
             × ⟨ fst y ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (arSubK : (ya yc b a ar c x : S) → ⟨ fst x ∈ fst (lookup (suc (suc (suc (suc zero))))
                                        (ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)) ⟩
           → ⟨ fst x ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (envInK : (E ya yc b a ar c z : S) → ⟨ (z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
               envOverAt zero (suc (suc (suc (suc (suc (suc zero))))))
                           (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) ⟩
           → ⟨ fst z ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (t0eq : fst (lookup (suc (suc (suc (suc (suc (suc t0)))))) γ) ≡ fst (numeralL 0))
  (t1eq : fst (lookup (suc (suc (suc (suc (suc (suc t1)))))) γ) ≡ fst (numeralL 1))
  (t0K : ⟨ fst (lookup (suc (suc (suc (suc (suc (suc t0)))))) γ)
           ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (tmKeyK : (k : S) → ⟨ fst k ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (num1K : ⟨ fst (numeralL 1) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (wKfact : (E ya yc b a ar c z w : S) → ⟨ (w ∷ z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
              tmValAt (suc (suc (suc (suc (suc (suc zero))))))
                      (suc zero)
                      zero ⟩
          → ⟨ fst w ∈ fst (lookup (eight (six K))
               (z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)) ⟩)
  (consK : (E ya yc b a ar c z w x e' : S) → ⟨ (e' ∷ x ∷ w ∷ z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
               consAtL zero (suc zero) (suc (suc (suc zero))) ⟩
          → ⟨ fst e' ∈ fst (lookup (ten (six K))
               (x ∷ w ∷ z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)) ⟩) where

  module A = ExInAgree {11 + n} (suc (suc zero)) (suc zero) zero
               (suc (suc (suc (suc (suc (suc N11))))))
               (suc (suc (suc (suc (suc (suc K))))))
               (suc (suc (suc (suc (suc (suc t0))))))
               (suc (suc (suc (suc (suc (suc t1)))))) γ
               tagEq numK innerK pairK codesK valK succK keyK subK envK entryK
               arSubK envInK t0eq t1eq t0K tmKeyK num1K wKfact consK

  row : Formula S (11 + n)
  row = ExIn.exInBndAt {11 + n} (suc (suc zero)) (suc zero) zero
          (suc (suc (suc (suc (suc (suc N11))))))
          (suc (suc (suc (suc (suc (suc K))))))
          (suc (suc (suc (suc (suc (suc t0))))))
          (suc (suc (suc (suc (suc (suc t1))))))

  out : ⟨ γ ⊨ exInClauseAt (suc (suc zero)) (suc zero) zero ⟩ → ⟨ γ ⊨ row ⟩
  out = A.out

  back : ⟨ γ ⊨ row ⟩ → ⟨ γ ⊨ exInClauseAt (suc (suc zero)) (suc zero) zero ⟩
  back = A.back

-- =====================================================================
-- THE TWELVE-ROW CONJUNCTION AT THE TWELVE FRAME.  The row transfers
-- are parameters; the composition threads the conjunction.
-- =====================================================================
module TwelveAgree {n : ℕ}
  (N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K : Fin (5 + n))
  (γ : S ^ (11 + n))
  (mem-out : ⟨ γ ⊨ memClauseAt (suc (suc zero)) (suc zero) zero ⟩
           → ⟨ γ ⊨ Mem.memBndAt {11 + n} (suc (suc zero)) (suc zero) zero
                 (suc (suc (suc (suc (suc (suc N0))))))
                 (suc (suc (suc (suc (suc (suc K))))))
                 (suc (suc (suc (suc (suc (suc t0))))))
                 (suc (suc (suc (suc (suc (suc t1)))))) ⟩)
  (mem-back : ⟨ γ ⊨ Mem.memBndAt {11 + n} (suc (suc zero)) (suc zero) zero
                 (suc (suc (suc (suc (suc (suc N0))))))
                 (suc (suc (suc (suc (suc (suc K))))))
                 (suc (suc (suc (suc (suc (suc t0))))))
                 (suc (suc (suc (suc (suc (suc t1)))))) ⟩
           → ⟨ γ ⊨ memClauseAt (suc (suc zero)) (suc zero) zero ⟩)
  (eq-out : ⟨ γ ⊨ eqClauseAt (suc (suc zero)) (suc zero) zero ⟩
          → ⟨ γ ⊨ Eq.eqBndAt {11 + n} (suc (suc zero)) (suc zero) zero
                (suc (suc (suc (suc (suc (suc N1))))))
                (suc (suc (suc (suc (suc (suc K))))))
                (suc (suc (suc (suc (suc (suc t0))))))
                (suc (suc (suc (suc (suc (suc t1)))))) ⟩)
  (eq-back : ⟨ γ ⊨ Eq.eqBndAt {11 + n} (suc (suc zero)) (suc zero) zero
                (suc (suc (suc (suc (suc (suc N1))))))
                (suc (suc (suc (suc (suc (suc K))))))
                (suc (suc (suc (suc (suc (suc t0))))))
                (suc (suc (suc (suc (suc (suc t1)))))) ⟩
          → ⟨ γ ⊨ eqClauseAt (suc (suc zero)) (suc zero) zero ⟩)
  (and-out : ⟨ γ ⊨ andClauseAt (suc (suc zero)) (suc zero) ⟩
           → ⟨ γ ⊨ And.andBndAt {11 + n} (suc (suc zero)) (suc zero) zero
                 (suc (suc (suc (suc (suc (suc N2))))))
                 (suc (suc (suc (suc (suc (suc K)))))) ⟩)
  (and-back : ⟨ γ ⊨ And.andBndAt {11 + n} (suc (suc zero)) (suc zero) zero
                 (suc (suc (suc (suc (suc (suc N2))))))
                 (suc (suc (suc (suc (suc (suc K)))))) ⟩
           → ⟨ γ ⊨ andClauseAt (suc (suc zero)) (suc zero) ⟩)
  (or-out : ⟨ γ ⊨ orClauseAt (suc (suc zero)) (suc zero) ⟩
          → ⟨ γ ⊨ Or.orBndAt {11 + n} (suc (suc zero)) (suc zero) zero
                (suc (suc (suc (suc (suc (suc N3))))))
                (suc (suc (suc (suc (suc (suc K)))))) ⟩)
  (or-back : ⟨ γ ⊨ Or.orBndAt {11 + n} (suc (suc zero)) (suc zero) zero
                (suc (suc (suc (suc (suc (suc N3))))))
                (suc (suc (suc (suc (suc (suc K)))))) ⟩
          → ⟨ γ ⊨ orClauseAt (suc (suc zero)) (suc zero) ⟩)
  (imp-out : ⟨ γ ⊨ impClauseAt (suc (suc zero)) (suc zero) zero ⟩
           → ⟨ γ ⊨ Imp.impBndAt {11 + n} (suc (suc zero)) (suc zero) zero
                 (suc (suc (suc (suc (suc (suc N4))))))
                 (suc (suc (suc (suc (suc (suc K)))))) ⟩)
  (imp-back : ⟨ γ ⊨ Imp.impBndAt {11 + n} (suc (suc zero)) (suc zero) zero
                 (suc (suc (suc (suc (suc (suc N4))))))
                 (suc (suc (suc (suc (suc (suc K)))))) ⟩
           → ⟨ γ ⊨ impClauseAt (suc (suc zero)) (suc zero) zero ⟩)
  (neg-out : ⟨ γ ⊨ negClauseAt (suc (suc zero)) (suc zero) zero ⟩
           → ⟨ γ ⊨ Neg.negBndAt {11 + n} (suc (suc zero)) (suc zero) zero
                 (suc (suc (suc (suc (suc (suc N5))))))
                 (suc (suc (suc (suc (suc (suc K)))))) ⟩)
  (neg-back : ⟨ γ ⊨ Neg.negBndAt {11 + n} (suc (suc zero)) (suc zero) zero
                 (suc (suc (suc (suc (suc (suc N5))))))
                 (suc (suc (suc (suc (suc (suc K)))))) ⟩
           → ⟨ γ ⊨ negClauseAt (suc (suc zero)) (suc zero) zero ⟩)
  (top-out : ⟨ γ ⊨ topClauseAt (suc (suc zero)) (suc zero) zero ⟩
           → ⟨ γ ⊨ Top.topBndAt {11 + n} (suc (suc zero)) (suc zero) zero
                 (suc (suc (suc (suc (suc (suc N6))))))
                 (suc (suc (suc (suc (suc (suc K)))))) ⟩)
  (top-back : ⟨ γ ⊨ Top.topBndAt {11 + n} (suc (suc zero)) (suc zero) zero
                 (suc (suc (suc (suc (suc (suc N6))))))
                 (suc (suc (suc (suc (suc (suc K)))))) ⟩
           → ⟨ γ ⊨ topClauseAt (suc (suc zero)) (suc zero) zero ⟩)
  (bot-out : ⟨ γ ⊨ botClauseAt (suc (suc zero)) (suc zero) ⟩
           → ⟨ γ ⊨ Bot.botBndAt {11 + n} (suc (suc zero)) (suc zero) zero
                 (suc (suc (suc (suc (suc (suc N7))))))
                 (suc (suc (suc (suc (suc (suc K)))))) ⟩)
  (bot-back : ⟨ γ ⊨ Bot.botBndAt {11 + n} (suc (suc zero)) (suc zero) zero
                 (suc (suc (suc (suc (suc (suc N7))))))
                 (suc (suc (suc (suc (suc (suc K)))))) ⟩
           → ⟨ γ ⊨ botClauseAt (suc (suc zero)) (suc zero) ⟩)
  (exist-out : ⟨ γ ⊨ existClauseAt (suc (suc zero)) (suc zero) zero ⟩
             → ⟨ γ ⊨ Exist.existBndAt {11 + n} (suc (suc zero)) (suc zero) zero
                   (suc (suc (suc (suc (suc (suc N8))))))
                   (suc (suc (suc (suc (suc (suc K)))))) ⟩)
  (exist-back : ⟨ γ ⊨ Exist.existBndAt {11 + n} (suc (suc zero)) (suc zero) zero
                   (suc (suc (suc (suc (suc (suc N8))))))
                   (suc (suc (suc (suc (suc (suc K)))))) ⟩
             → ⟨ γ ⊨ existClauseAt (suc (suc zero)) (suc zero) zero ⟩)
  (forall-out : ⟨ γ ⊨ forallClauseAt (suc (suc zero)) (suc zero) zero ⟩
              → ⟨ γ ⊨ Forall.forallBndAt {11 + n} (suc (suc zero)) (suc zero) zero
                    (suc (suc (suc (suc (suc (suc N9))))))
                    (suc (suc (suc (suc (suc (suc K)))))) ⟩)
  (forall-back : ⟨ γ ⊨ Forall.forallBndAt {11 + n} (suc (suc zero)) (suc zero) zero
                    (suc (suc (suc (suc (suc (suc N9))))))
                    (suc (suc (suc (suc (suc (suc K)))))) ⟩
              → ⟨ γ ⊨ forallClauseAt (suc (suc zero)) (suc zero) zero ⟩)
  (allin-out : ⟨ γ ⊨ allInClauseAt (suc (suc zero)) (suc zero) zero ⟩
             → ⟨ γ ⊨ AllIn.allInBndAt {11 + n} (suc (suc zero)) (suc zero) zero
                   (suc (suc (suc (suc (suc (suc N10))))))
                   (suc (suc (suc (suc (suc (suc K))))))
                   (suc (suc (suc (suc (suc (suc t0))))))
                   (suc (suc (suc (suc (suc (suc t1)))))) ⟩)
  (allin-back : ⟨ γ ⊨ AllIn.allInBndAt {11 + n} (suc (suc zero)) (suc zero) zero
                   (suc (suc (suc (suc (suc (suc N10))))))
                   (suc (suc (suc (suc (suc (suc K))))))
                   (suc (suc (suc (suc (suc (suc t0))))))
                   (suc (suc (suc (suc (suc (suc t1)))))) ⟩
             → ⟨ γ ⊨ allInClauseAt (suc (suc zero)) (suc zero) zero ⟩)
  (exin-out : ⟨ γ ⊨ exInClauseAt (suc (suc zero)) (suc zero) zero ⟩
            → ⟨ γ ⊨ ExIn.exInBndAt {11 + n} (suc (suc zero)) (suc zero) zero
                  (suc (suc (suc (suc (suc (suc N11))))))
                  (suc (suc (suc (suc (suc (suc K))))))
                  (suc (suc (suc (suc (suc (suc t0))))))
                  (suc (suc (suc (suc (suc (suc t1)))))) ⟩)
  (exin-back : ⟨ γ ⊨ ExIn.exInBndAt {11 + n} (suc (suc zero)) (suc zero) zero
                  (suc (suc (suc (suc (suc (suc N11))))))
                  (suc (suc (suc (suc (suc (suc K))))))
                  (suc (suc (suc (suc (suc (suc t0))))))
                  (suc (suc (suc (suc (suc (suc t1)))))) ⟩
            → ⟨ γ ⊨ exInClauseAt (suc (suc zero)) (suc zero) zero ⟩) where

  twelveB : Formula S (11 + n)
  twelveB =
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
    ∧̇ (Top.topBndAt {11 + n} (suc (suc zero)) (suc zero) zero
      (suc (suc (suc (suc (suc (suc N6))))))
      (suc (suc (suc (suc (suc (suc K))))))
    ∧̇ (Bot.botBndAt {11 + n} (suc (suc zero)) (suc zero) zero
      (suc (suc (suc (suc (suc (suc N7))))))
      (suc (suc (suc (suc (suc (suc K))))))
    ∧̇ (Exist.existBndAt {11 + n} (suc (suc zero)) (suc zero) zero
      (suc (suc (suc (suc (suc (suc N8))))))
      (suc (suc (suc (suc (suc (suc K))))))
    ∧̇ (Forall.forallBndAt {11 + n} (suc (suc zero)) (suc zero) zero
      (suc (suc (suc (suc (suc (suc N9))))))
      (suc (suc (suc (suc (suc (suc K))))))
    ∧̇ (AllIn.allInBndAt {11 + n} (suc (suc zero)) (suc zero) zero
      (suc (suc (suc (suc (suc (suc N10))))))
      (suc (suc (suc (suc (suc (suc K))))))
      (suc (suc (suc (suc (suc (suc t0))))))
      (suc (suc (suc (suc (suc (suc t1))))))
    ∧̇ ExIn.exInBndAt {11 + n} (suc (suc zero)) (suc zero) zero
      (suc (suc (suc (suc (suc (suc N11))))))
      (suc (suc (suc (suc (suc (suc K))))))
      (suc (suc (suc (suc (suc (suc t0))))))
      ((suc (suc (suc (suc (suc (suc t1)))))))))))))))))

  out : ⟨ γ ⊨ twelveAt (suc (suc zero)) (suc zero) zero ⟩ → ⟨ γ ⊨ twelveB ⟩
  out h =
    ( mem-out (h .fst)
    , ( eq-out (h .snd .fst)
      , ( and-out (h .snd .snd .fst)
        , ( or-out (h .snd .snd .snd .fst)
          , ( imp-out (h .snd .snd .snd .snd .fst)
            , ( neg-out (h .snd .snd .snd .snd .snd .fst)
              , ( top-out (h .snd .snd .snd .snd .snd .snd .fst)
                , ( bot-out (h .snd .snd .snd .snd .snd .snd .snd .fst)
                  , ( exist-out (h .snd .snd .snd .snd .snd .snd .snd .snd .fst)
                    , ( forall-out (h .snd .snd .snd .snd .snd .snd .snd .snd .snd .fst)
                      , ( allin-out (h .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .fst)
                        , exin-out (h .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd) )))))))))))

  back : ⟨ γ ⊨ twelveB ⟩ → ⟨ γ ⊨ twelveAt (suc (suc zero)) (suc zero) zero ⟩
  back h =
    ( mem-back (h .fst)
    , ( eq-back (h .snd .fst)
      , ( and-back (h .snd .snd .fst)
        , ( or-back (h .snd .snd .snd .fst)
          , ( imp-back (h .snd .snd .snd .snd .fst)
            , ( neg-back (h .snd .snd .snd .snd .snd .fst)
              , ( top-back (h .snd .snd .snd .snd .snd .snd .fst)
                , ( bot-back (h .snd .snd .snd .snd .snd .snd .snd .fst)
                  , ( exist-back (h .snd .snd .snd .snd .snd .snd .snd .snd .fst)
                    , ( forall-back (h .snd .snd .snd .snd .snd .snd .snd .snd .snd .fst)
                      , ( allin-back (h .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .fst)
                        , exin-back (h .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd) )))))))))))

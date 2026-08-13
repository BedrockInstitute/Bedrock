{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.55] probe A: the slot-convention question, tested before the
-- build.  Two halves.
--
-- HALF 1 (the negative): the K-only parameterization cannot
-- instantiate at the twelve frame.  The agreement's row places B at
-- `suc B`; the twelve frame places B at `zero`.  Matching them is the
-- equation `suc B ≡ zero`, which has no solution in Fin
-- (no-suc-zero).  K is not the only hard-coded slot; the whole row
-- tuple is shifted by the suc convention, with slot 0 reserved.
--
-- HALF 2 (the positive): the full slot parameterization works.  The
-- generalized BotAgree takes (C T B N K : Fin m) at the row frame
-- directly, reads lookup C / lookup K at that frame, and instantiates
-- at the twelve frame's Bot row (C = 2, T = 1, B = 0, N = suc^6 N7,
-- K = suc^6 K) with no re-indexing.  The proof body is the master's
-- BotAgree body with the slot renames only.
--
-- Untracked probe; never committed.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ155A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

import FOL.Absoluteness
open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Axioms.Numerals {ℓ} using ( numeralL )
open import L.Coding.Model {ℓ}
  using ( arityTagAtL; arityTagAtL-adequate; botClauseAt; emptyAt; prʟ )
open import L.Condensation {ℓ} lem using
  ( module Bot; module UnaryShape
  ; arTagB; emptyB
  ; emptyAt→emptyB; emptyB→emptyAt )

open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet using ( #_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Data.Unit using ( Unit; tt )
import Cubical.Data.Empty as Empty
open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- =====================================================================
-- HALF 1: the K-only parameterization still cannot hit slot 0.
-- The agreement row places B at `suc B`; the twelve frame places B at
-- `zero`.  No Fin element satisfies `suc B ≡ zero`.
-- =====================================================================
no-suc-zero : {n : ℕ} (B : Fin n) → (suc B ≡ zero) → Empty.⊥
no-suc-zero {n} B p =
  subst (λ { zero → Empty.⊥ ; (suc _) → Unit }) p tt

-- =====================================================================
-- HALF 2: the full slot parameterization, proven on the Bot row.
-- The signature takes the row slots directly at the row frame.
-- =====================================================================
module BotAgreeGen {m : ℕ} (C T B N K : Fin m) (γ : S ^ m)
  (tagEq : fst (lookup N γ) ≡ fst (numeralL 7))
  (numK : ⟨ fst (numeralL 7) ∈ fst (lookup K γ) ⟩)
  (innerK : (a : S) → ⟨ fst (prʟ (numeralL 7) a) ∈ fst (lookup K γ) ⟩)
  (codesK : (c ar a : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
           → fst c ≡ pr (fst ar) (pr (# 7) (fst a))
           → ⟨ fst ar ∈ fst (lookup K γ) ⟩ × ⟨ fst a ∈ fst (lookup K γ) ⟩)
  (valK : (c ar a yc : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
         → fst c ≡ pr (fst ar) (pr (# 7) (fst a))
         → ⟨ fst yc ∈ fst (lookup K γ) ⟩) where

  private
    φB : Formula S m
    φB = Bot.botBndAt C T B N K

  bot-out : ⟨ γ ⊨ botClauseAt C T ⟩ → ⟨ γ ⊨ φB ⟩
  bot-out h = λ c c∈ ar arK a aK yc ycK shB hc →
    let shD = UnaryShape.out {m = m} N K 7 (yc ∷ a ∷ ar ∷ c ∷ γ) tagEq shB
        hb = h c c∈ ar a yc shD hc
    in emptyAt→emptyB zero (suc (suc (suc (suc K)))) (yc ∷ a ∷ ar ∷ c ∷ γ) hb

  bot-in : ⟨ γ ⊨ φB ⟩ → ⟨ γ ⊨ botClauseAt C T ⟩
  bot-in h = λ c c∈ ar a yc shD hc →
    let shEq : fst c ≡ pr (fst ar) (pr (# 7) (fst a))
        shEq = transport (cong fst (arityTagAtL-adequate (suc (suc (suc zero)))
                 (suc (suc zero)) 7 (suc zero) (yc ∷ a ∷ ar ∷ c ∷ γ))) shD
        (arK , aK) = codesK c ar a c∈ shEq
        ycK = valK c ar a yc c∈ shEq
        shB = UnaryShape.in' {m = m} N K 7 (yc ∷ a ∷ ar ∷ c ∷ γ) tagEq numK innerK shD
        hb = h c c∈ ar arK a aK yc ycK shB hc
    in emptyB→emptyAt zero (suc (suc (suc (suc K)))) (yc ∷ a ∷ ar ∷ c ∷ γ) hb

-- =====================================================================
-- HALF 2b: the generalized agreement instantiates at the twelve
-- frame's Bot row with no re-indexing: C = 2, T = 1, B = 0,
-- N = suc^6 N7, K = suc^6 K, at arity 11 + n.
-- =====================================================================
module TwelveBot {n : ℕ} (N7 K : Fin (5 + n)) (γ : S ^ (11 + n))
  (tagEq : fst (lookup (suc (suc (suc (suc (suc (suc N7)))))) γ)
         ≡ fst (numeralL 7))
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

  module G = BotAgreeGen {11 + n} (suc (suc zero)) (suc zero) zero
               (suc (suc (suc (suc (suc (suc N7))))))
               (suc (suc (suc (suc (suc (suc K)))))) γ
               tagEq numK innerK codesK valK

  row : Formula S (11 + n)
  row = Bot.botBndAt {11 + n} (suc (suc zero)) (suc zero) zero
          (suc (suc (suc (suc (suc (suc N7))))))
          (suc (suc (suc (suc (suc (suc K))))))

  out : ⟨ γ ⊨ botClauseAt (suc (suc zero)) (suc zero) ⟩ → ⟨ γ ⊨ row ⟩
  out = G.bot-out

  back : ⟨ γ ⊨ row ⟩ → ⟨ γ ⊨ botClauseAt (suc (suc zero)) (suc zero) ⟩
  back = G.bot-in

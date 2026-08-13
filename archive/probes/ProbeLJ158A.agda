{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.58] probe A: the walk in the cheapest spelling, master-import
-- only.  The consumer of the leaf adequacy ([LJ-1.52] Probe A/B, the
-- levelIn/cover routes) needs the story -> machine direction only
-- (DefBodyB -> DefBody), so this probe carries `back` everywhere and
-- drops the machine -> story direction, the code-set membership and
-- the component-in-K site facts that only that direction consumed.
-- The twelve-row disjunction assembly is a generic lift kit at
-- abstract propositions, so the full formula trees normalize once per
-- statement instead of once per helper.
--
-- Untracked probe; never committed.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ158A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

import FOL.Absoluteness
open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _∧̇_; _∨̇_; _≐_; _∈̇_; ∃̇_; ∃̇∈; ⊤̇ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )
open import L.Coding.Model {ℓ}
  using ( prAtL; prAtL-adequate; arityTagAtL; arityTagAtL-adequate
        ; arityTagPairAtL; arityTagPairAtL-adequate; tagAtL; tagAtL-adequate
        ; tagPairAtL; tagPairAtL-adequate; prʟ; prʟ-fst )
open import L.Coding.Shape {ℓ}
  using ( isTmAt; shapes; binForm; unForm; bothTm; fstTm; noneB; noneU; zeroPay )
open import L.Condensation {ℓ} lem using
  ( arTagBS; arTagPairBS; tagBS; isTmBS; bothTmBS; fstTmBS
  ; binFormBS; unFormBS; shapesBS )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet using ( #_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- =====================================================================
-- SECTION 1. THE SHAPE TRANSFERS, STORY -> MACHINE ONLY.
-- arTagBS tag K against arityTagAtL k, and arTagPairBS tag K against
-- arityTagPairAtL k, at the 3- and 4-deep frames.  Ported from
-- ProbeLJ156A section 1, `out` only.
-- =====================================================================
module UnShapeClosed {m : ℕ} (tag K : Fin m) (k : ℕ) (γ : S ^ (3 + m))
  (tagEq : fst (lookup (suc (suc (suc tag))) γ) ≡ fst (numeralL k))
  (numK : ⟨ fst (numeralL k) ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (innerK : (a : S) → ⟨ fst (prʟ (numeralL k) a) ∈ fst (lookup (suc (suc (suc K))) γ) ⟩) where

  out : ⟨ γ ⊨ arTagBS tag K ⟩
      → ⟨ γ ⊨ arityTagAtL (suc (suc zero)) (suc zero) k zero ⟩
  out h = transport (cong fst (sym (arityTagAtL-adequate (suc (suc zero))
             (suc zero) k zero γ))) target
    where
    target : fst (lookup (suc (suc zero)) γ)
           ≡ pr (fst (lookup (suc zero) γ)) (pr (# k) (fst (lookup zero γ)))
    target = PT.rec (setIsSet _ _)
      (λ { (z , (z∈ , (p , kz))) → PT.rec (setIsSet _ _)
        (λ { (t , (t∈ , (tp , zt))) →
          let ar₀ = fst (lookup (suc zero) γ)
              a₀ = fst (lookup zero γ)
              p' : fst (lookup (suc (suc (suc zero))) (z ∷ γ))
                  ≡ pr (fst (lookup (suc (suc zero)) (z ∷ γ)))
                       (fst (lookup zero (z ∷ γ)))
              p' = transport (cong fst (prAtL-adequate (suc (suc (suc zero)))
                    (suc (suc zero)) zero (z ∷ γ))) p
              zt' : fst (lookup (suc zero) (t ∷ z ∷ γ))
                   ≡ pr (fst (lookup zero (t ∷ z ∷ γ)))
                        (fst (lookup (suc (suc zero)) (t ∷ z ∷ γ)))
              zt' = transport (cong fst (prAtL-adequate (suc zero) zero
                    (suc (suc zero)) (t ∷ z ∷ γ))) zt
              tp' : fst (lookup zero (t ∷ z ∷ γ))
                  ≡ fst (lookup (suc (suc (suc tag))) γ)
              tp' = tp
          in p' ∙ cong (pr ar₀) zt'
               ∙ cong (λ v → pr ar₀ (pr v a₀))
                      (tp' ∙ tagEq ∙ numeralL-fst k) })
        kz })
      h

module BinShapeClosed {m : ℕ} (tag K : Fin m) (k : ℕ) (γ : S ^ (4 + m))
  (tagEq : fst (lookup (suc (suc (suc (suc tag)))) γ) ≡ fst (numeralL k))
  (numK : ⟨ fst (numeralL k) ∈ fst (lookup (suc (suc (suc (suc K)))) γ) ⟩)
  (innerK : (a b : S) → ⟨ fst (prʟ (numeralL k) (prʟ a b)) ∈ fst (lookup (suc (suc (suc (suc K)))) γ) ⟩)
  (pairK : (a b : S) → ⟨ fst (prʟ a b) ∈ fst (lookup (suc (suc (suc (suc K)))) γ) ⟩) where

  out : ⟨ γ ⊨ arTagPairBS tag K ⟩
      → ⟨ γ ⊨ arityTagPairAtL (suc (suc (suc zero))) (suc (suc zero)) k (suc zero) zero ⟩
  out h = transport (cong fst (sym (arityTagPairAtL-adequate (suc (suc (suc zero)))
             (suc (suc zero)) k (suc zero) zero γ))) target
    where
    target : fst (lookup (suc (suc (suc zero))) γ)
           ≡ pr (fst (lookup (suc (suc zero)) γ))
                (pr (# k) (pr (fst (lookup (suc zero) γ)) (fst (lookup zero γ))))
    target = PT.rec (setIsSet _ _)
      (λ { (z , (z∈ , (p , kz))) → PT.rec (setIsSet _ _)
        (λ { (t , (t∈ , kt)) → PT.rec (setIsSet _ _)
          (λ { (w , (w∈ , (tp , (zt , wb)))) →
            let ar₀ = fst (lookup (suc (suc zero)) γ)
                p' : fst (lookup (suc (suc (suc (suc zero)))) (z ∷ γ))
                    ≡ pr (fst (lookup (suc (suc (suc zero))) (z ∷ γ)))
                         (fst (lookup zero (z ∷ γ)))
                p' = transport (cong fst (prAtL-adequate (suc (suc (suc (suc zero))))
                      (suc (suc (suc zero))) zero (z ∷ γ))) p
                zt' : fst (lookup (suc (suc zero)) (w ∷ t ∷ z ∷ γ))
                     ≡ pr (fst (lookup (suc zero) (w ∷ t ∷ z ∷ γ)))
                          (fst (lookup zero (w ∷ t ∷ z ∷ γ)))
                zt' = transport (cong fst (prAtL-adequate (suc (suc zero)) (suc zero) zero
                      (w ∷ t ∷ z ∷ γ))) zt
                wb' : fst (lookup zero (w ∷ t ∷ z ∷ γ))
                     ≡ pr (fst (lookup (suc (suc (suc (suc zero)))) (w ∷ t ∷ z ∷ γ)))
                          (fst (lookup (suc (suc (suc zero))) (w ∷ t ∷ z ∷ γ)))
                wb' = transport (cong fst (prAtL-adequate zero (suc (suc (suc (suc zero))))
                      (suc (suc (suc zero))) (w ∷ t ∷ z ∷ γ))) wb
                tp' : fst (lookup (suc zero) (w ∷ t ∷ z ∷ γ))
                    ≡ fst (lookup (suc (suc (suc (suc tag)))) γ)
                tp' = tp
            in p' ∙ cong (pr ar₀) (zt' ∙ cong (pr (fst (lookup (suc zero) (w ∷ t ∷ z ∷ γ)))) wb')
                 ∙ cong (λ v → pr ar₀ (pr v (pr (fst (lookup (suc zero) γ)) (fst (lookup zero γ)))))
                        (tp' ∙ tagEq ∙ numeralL-fst k) })
          kt })
        kz })
      h

-- =====================================================================
-- SECTION 2. THE TERM SHAPE TRANSFER, STORY -> MACHINE ONLY.
-- isTmBS t A K N0 N1 against isTmAt t, both branches.  Ported from
-- ProbeLJ156A section 6, `out` only; the carrierK/arityK facts were
-- consumed by the machine -> story direction only and are dropped.
-- =====================================================================
module TmBranch {m : ℕ} (t : Fin (4 + m)) (tag : Fin m) (k : ℕ)
  (x : Fin (4 + m)) (K : Fin m) (γ : S ^ (4 + m))
  (tagEq : fst (lookup (suc (suc (suc (suc tag)))) γ) ≡ fst (numeralL k))
  (numK : ⟨ fst (numeralL k) ∈ fst (lookup (suc (suc (suc (suc K)))) γ) ⟩) where

  story : Formula S (4 + m)
  story = ∃̇∈ (var (suc (suc (suc (suc K)))))
            (tagBS (suc t) (suc (suc (suc (suc (suc tag))))) zero
                   (suc (suc (suc (suc (suc K)))))
            ∧̇ (var zero ∈̇ var (suc x)))

  machine : Formula S (4 + m)
  machine = ∃̇ (tagAtL (suc t) k zero ∧̇ (var zero ∈̇ var (suc x)))

  out : ⟨ γ ⊨ story ⟩ → ⟨ γ ⊨ machine ⟩
  out h = PT.rec squash₁ go h
    where
    go : Σ[ v ∈ S ] (⟨ fst v ∈ fst (lookup (suc (suc (suc (suc K)))) γ) ⟩
                    × ⟨ (v ∷ γ) ⊨ tagBS (suc t) (suc (suc (suc (suc (suc tag))))) zero
                                        (suc (suc (suc (suc (suc K)))))
                         ∧̇ (var zero ∈̇ var (suc x)) ⟩)
       → ⟨ γ ⊨ machine ⟩
    go (v , (vK , (hTag , vx))) = ∣ v , ( tagAt , vx ) ∣₁
      where
      tagAt : ⟨ (v ∷ γ) ⊨ tagAtL (suc t) k zero ⟩
      tagAt = transport (cong fst (sym (tagAtL-adequate {5 + m} (suc t) k zero (v ∷ γ))))
        (PT.rec (setIsSet _ _)
          (λ { (z , (zK , (ze , zp))) →
            let zp' : fst (lookup (suc (suc t)) (z ∷ v ∷ γ))
                     ≡ pr (fst (lookup zero (z ∷ v ∷ γ)))
                          (fst (lookup (suc zero) (z ∷ v ∷ γ)))
                zp' = transport (cong fst (prAtL-adequate (suc (suc t)) zero
                      (suc zero) (z ∷ v ∷ γ))) zp
            in zp' ∙ cong (λ w → pr w (fst (lookup (suc zero) (z ∷ v ∷ γ))))
                         (ze ∙ tagEq ∙ numeralL-fst k) })
          hTag)

module TmAgree {m : ℕ} (t : Fin (4 + m)) (A K N0 N1 : Fin m) (γ : S ^ (4 + m))
  (tagEq0 : fst (lookup (suc (suc (suc (suc N0)))) γ) ≡ fst (numeralL 0))
  (tagEq1 : fst (lookup (suc (suc (suc (suc N1)))) γ) ≡ fst (numeralL 1))
  (numK0 : ⟨ fst (numeralL 0) ∈ fst (lookup (suc (suc (suc (suc K)))) γ) ⟩)
  (numK1 : ⟨ fst (numeralL 1) ∈ fst (lookup (suc (suc (suc (suc K)))) γ) ⟩) where

  module B0 = TmBranch {m} t N0 0 (suc (suc (suc (suc A)))) K γ
               tagEq0 numK0
  module B1 = TmBranch {m} t N1 1 (suc (suc zero)) K γ
               tagEq1 numK1

  out : ⟨ γ ⊨ isTmBS t A K N0 N1 ⟩ → ⟨ γ ⊨ isTmAt t (suc (suc zero)) (suc (suc (suc (suc A)))) ⟩
  out h = PT.rec squash₁
    (λ { (inl h0) → ∣ inl (B0.out h0) ∣₁
       ; (inr h1) → ∣ inr (B1.out h1) ∣₁ })
    h

-- =====================================================================
-- SECTION 3. THE RELATIONS, STORY -> MACHINE ONLY.
-- Rows 0/1 carry bothTmBS against bothTm; rows 10/11 carry fstTmBS
-- against fstTm; rows 2/3/4/5/8/9 carry top against top; rows 6/7
-- carry the bounded zero-pin against the machine's constant zero.
-- Ported from ProbeLJ157A section 2, `out` only.
-- =====================================================================
module BothTmRel {n : ℕ} (A K N0 N1 : Fin n) (γ : S ^ (1 + n))
  (tagEq0 : fst (lookup (suc N0) γ) ≡ fst (numeralL 0))
  (tagEq1 : fst (lookup (suc N1) γ) ≡ fst (numeralL 1))
  (numK0 : ⟨ fst (numeralL 0) ∈ fst (lookup (suc K) γ) ⟩)
  (numK1 : ⟨ fst (numeralL 1) ∈ fst (lookup (suc K) γ) ⟩) where

  out : (b a N : S) → ⟨ (b ∷ a ∷ N ∷ γ) ⊨ bothTmBS A K N0 N1 ⟩
                    → ⟨ (b ∷ a ∷ N ∷ γ) ⊨ bothTm A ⟩
  out b a N (h0 , h1) = (B0.out h0 , B1.out h1)
    where
    module B0 = TmAgree {n} (suc zero) A K N0 N1 (b ∷ a ∷ N ∷ γ)
                   tagEq0 tagEq1 numK0 numK1
    module B1 = TmAgree {n} zero A K N0 N1 (b ∷ a ∷ N ∷ γ)
                   tagEq0 tagEq1 numK0 numK1

module FstTmRel {n : ℕ} (A K N0 N1 : Fin n) (γ : S ^ (1 + n))
  (tagEq0 : fst (lookup (suc N0) γ) ≡ fst (numeralL 0))
  (tagEq1 : fst (lookup (suc N1) γ) ≡ fst (numeralL 1))
  (numK0 : ⟨ fst (numeralL 0) ∈ fst (lookup (suc K) γ) ⟩)
  (numK1 : ⟨ fst (numeralL 1) ∈ fst (lookup (suc K) γ) ⟩) where

  out : (b a N : S) → ⟨ (b ∷ a ∷ N ∷ γ) ⊨ fstTmBS A K N0 N1 ⟩
                    → ⟨ (b ∷ a ∷ N ∷ γ) ⊨ fstTm A ⟩
  out b a N = B.out
    where
    module B = TmAgree {n} (suc zero) A K N0 N1 (b ∷ a ∷ N ∷ γ)
                  tagEq0 tagEq1 numK0 numK1

module TopBinRel {n : ℕ} (γ : S ^ (1 + n)) where
  out : (b a N : S) → ⟨ (b ∷ a ∷ N ∷ γ) ⊨ ⊤̇ {n = 4 + n} ⟩
                    → ⟨ (b ∷ a ∷ N ∷ γ) ⊨ ⊤̇ {n = 4 + n} ⟩
  out b a N h = h

module TopUnRel {n : ℕ} (γ : S ^ (1 + n)) where
  out : (a N : S) → ⟨ (a ∷ N ∷ γ) ⊨ ⊤̇ {n = 3 + n} ⟩
                  → ⟨ (a ∷ N ∷ γ) ⊨ ⊤̇ {n = 3 + n} ⟩
  out a N h = h

module ZeroPayRel {n : ℕ} (N0 : Fin n) (γ : S ^ (1 + n))
  (tagEq0 : fst (lookup (suc N0) γ) ≡ fst (numeralL 0)) where

  out : (a N : S) → ⟨ (a ∷ N ∷ γ) ⊨ (var zero ≐ var (suc (suc (suc N0)))) ⟩
                  → ⟨ (a ∷ N ∷ γ) ⊨ (var zero ≐ con (numeralL 0)) ⟩
  out a N h = h ∙ tagEq0

-- =====================================================================
-- SECTION 4. THE PER-ROW FRAME AGREEMENTS, STORY -> MACHINE ONLY.
-- binFormBS tag K relB against binForm k relM at the walk frame
-- γ : S ^ (1 + n), under the tag-pin and numeral-in-K facts.  Ported
-- from ProbeLJ157A section 1, `back` only; the code-set membership
-- and component-in-K facts are dropped with the machine -> story
-- direction.
-- =====================================================================
module BinFormAgree {n : ℕ} (tag K : Fin n) (k : ℕ)
  (γ : S ^ (1 + n))
  (tagEq : fst (lookup (suc tag) γ) ≡ fst (numeralL k))
  (numK : ⟨ fst (numeralL k) ∈ fst (lookup (suc K) γ) ⟩)
  (innerK : (a b : S) → ⟨ fst (prʟ (numeralL k) (prʟ a b)) ∈ fst (lookup (suc K) γ) ⟩)
  (pairK : (a b : S) → ⟨ fst (prʟ a b) ∈ fst (lookup (suc K) γ) ⟩)
  (relB relM : Formula S (4 + n))
  (relOut : (b a N : S) → ⟨ (b ∷ a ∷ N ∷ γ) ⊨ relB ⟩
          → ⟨ (b ∷ a ∷ N ∷ γ) ⊨ relM ⟩) where

  back : ⟨ γ ⊨ binFormBS tag K relB ⟩
       → ⟨ γ ⊨ binForm k relM ⟩
  back h = PT.rec squash₁ go h
    where
    go : Σ[ N ∈ S ] (⟨ fst N ∈ fst (lookup (suc K) γ) ⟩
                    × ⟨ (N ∷ γ) ⊨ ∃̇∈ (var (suc (suc K)))
                          (∃̇∈ (var (suc (suc (suc K))))
                            (arTagPairBS tag K ∧̇ relB)) ⟩)
       → ⟨ γ ⊨ binForm k relM ⟩
    go (N , (N∈ , hN)) = PT.rec squash₁ go₂ hN
      where
      go₂ : Σ[ a ∈ S ] (⟨ fst a ∈ fst (lookup (suc K) γ) ⟩
                       × ⟨ (a ∷ N ∷ γ) ⊨ ∃̇∈ (var (suc (suc (suc K))))
                             (arTagPairBS tag K ∧̇ relB) ⟩)
          → ⟨ γ ⊨ binForm k relM ⟩
      go₂ (a , (a∈ , ha)) = PT.rec squash₁ go₃ ha
        where
        go₃ : Σ[ b ∈ S ] (⟨ fst b ∈ fst (lookup (suc K) γ) ⟩
                         × ⟨ (b ∷ a ∷ N ∷ γ) ⊨ arTagPairBS tag K ∧̇ relB ⟩)
            → ⟨ γ ⊨ binForm k relM ⟩
        go₃ (b , (b∈ , (hTag , hRel))) =
          ∣ N , ∣ a , ∣ b , ( S.out hTag , relOut b a N hRel ) ∣₁ ∣₁ ∣₁
          where
          module S = BinShapeClosed {n} tag K k (b ∷ a ∷ N ∷ γ)
                       tagEq numK innerK pairK

module UnFormAgree {n : ℕ} (tag K : Fin n) (k : ℕ)
  (γ : S ^ (1 + n))
  (tagEq : fst (lookup (suc tag) γ) ≡ fst (numeralL k))
  (numK : ⟨ fst (numeralL k) ∈ fst (lookup (suc K) γ) ⟩)
  (innerK : (a : S) → ⟨ fst (prʟ (numeralL k) a) ∈ fst (lookup (suc K) γ) ⟩)
  (relB relM : Formula S (3 + n))
  (relOut : (a N : S) → ⟨ (a ∷ N ∷ γ) ⊨ relB ⟩
          → ⟨ (a ∷ N ∷ γ) ⊨ relM ⟩) where

  back : ⟨ γ ⊨ unFormBS tag K relB ⟩
       → ⟨ γ ⊨ unForm k relM ⟩
  back h = PT.rec squash₁ go h
    where
    go : Σ[ N ∈ S ] (⟨ fst N ∈ fst (lookup (suc K) γ) ⟩
                    × ⟨ (N ∷ γ) ⊨ ∃̇∈ (var (suc (suc K)))
                          (arTagBS tag K ∧̇ relB) ⟩)
       → ⟨ γ ⊨ unForm k relM ⟩
    go (N , (N∈ , hN)) = PT.rec squash₁ go₂ hN
      where
      go₂ : Σ[ a ∈ S ] (⟨ fst a ∈ fst (lookup (suc K) γ) ⟩
                       × ⟨ (a ∷ N ∷ γ) ⊨ arTagBS tag K ∧̇ relB ⟩)
          → ⟨ γ ⊨ unForm k relM ⟩
      go₂ (a , (a∈ , (hTag , hRel))) =
        ∣ N , ∣ a , ( S.out hTag , relOut a N hRel ) ∣₁ ∣₁
        where
        module S = UnShapeClosed {n} tag K k (a ∷ N ∷ γ)
                     tagEq numK innerK

-- =====================================================================
-- SECTION 5. THE GENERIC TWELVE-WAY DISJUNCTION LIFT, BACK DIRECTION.
-- At abstract propositions the satisfaction is stuck, so the kit
-- checks as parameterized content; the concrete formula trees appear
-- only at the walk's two statements, where each normalizes once.
-- =====================================================================
module Lift12Back {n : ℕ} (γ : S ^ (1 + n))
  (P₀ P₁ P₂ P₃ P₄ P₅ P₆ P₇ P₈ P₉ P₁₀ P₁₁ : Type (ℓ-suc ℓ))
  (Q₀ Q₁ Q₂ Q₃ Q₄ Q₅ Q₆ Q₇ Q₈ Q₉ Q₁₀ Q₁₁ : Type (ℓ-suc ℓ))
  (r₀ : P₀ → Q₀) (r₁ : P₁ → Q₁) (r₂ : P₂ → Q₂) (r₃ : P₃ → Q₃)
  (r₄ : P₄ → Q₄) (r₅ : P₅ → Q₅) (r₆ : P₆ → Q₆) (r₇ : P₇ → Q₇)
  (r₈ : P₈ → Q₈) (r₉ : P₉ → Q₉) (r₁₀ : P₁₀ → Q₁₀) (r₁₁ : P₁₁ → Q₁₁) where

  s₁₀ : ∥ P₁₀ ⊎ P₁₁ ∥₁ → ∥ Q₁₀ ⊎ Q₁₁ ∥₁
  s₁₀ = PT.rec squash₁
    (λ { (inl x) → ∣ inl (r₁₀ x) ∣₁
       ; (inr x) → ∣ inr (r₁₁ x) ∣₁ })

  s₉ : ∥ P₉ ⊎ ∥ P₁₀ ⊎ P₁₁ ∥₁ ∥₁ → ∥ Q₉ ⊎ ∥ Q₁₀ ⊎ Q₁₁ ∥₁ ∥₁
  s₉ = PT.rec squash₁
    (λ { (inl x) → ∣ inl (r₉ x) ∣₁
       ; (inr x) → ∣ inr (s₁₀ x) ∣₁ })

  s₈ : ∥ P₈ ⊎ ∥ P₉ ⊎ ∥ P₁₀ ⊎ P₁₁ ∥₁ ∥₁ ∥₁
     → ∥ Q₈ ⊎ ∥ Q₉ ⊎ ∥ Q₁₀ ⊎ Q₁₁ ∥₁ ∥₁ ∥₁
  s₈ = PT.rec squash₁
    (λ { (inl x) → ∣ inl (r₈ x) ∣₁
       ; (inr x) → ∣ inr (s₉ x) ∣₁ })

  s₇ : ∥ P₇ ⊎ ∥ P₈ ⊎ ∥ P₉ ⊎ ∥ P₁₀ ⊎ P₁₁ ∥₁ ∥₁ ∥₁ ∥₁
     → ∥ Q₇ ⊎ ∥ Q₈ ⊎ ∥ Q₉ ⊎ ∥ Q₁₀ ⊎ Q₁₁ ∥₁ ∥₁ ∥₁ ∥₁
  s₇ = PT.rec squash₁
    (λ { (inl x) → ∣ inl (r₇ x) ∣₁
       ; (inr x) → ∣ inr (s₈ x) ∣₁ })

  s₆ : ∥ P₆ ⊎ ∥ P₇ ⊎ ∥ P₈ ⊎ ∥ P₉ ⊎ ∥ P₁₀ ⊎ P₁₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁
     → ∥ Q₆ ⊎ ∥ Q₇ ⊎ ∥ Q₈ ⊎ ∥ Q₉ ⊎ ∥ Q₁₀ ⊎ Q₁₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁
  s₆ = PT.rec squash₁
    (λ { (inl x) → ∣ inl (r₆ x) ∣₁
       ; (inr x) → ∣ inr (s₇ x) ∣₁ })

  s₅ : ∥ P₅ ⊎ ∥ P₆ ⊎ ∥ P₇ ⊎ ∥ P₈ ⊎ ∥ P₉ ⊎ ∥ P₁₀ ⊎ P₁₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁
     → ∥ Q₅ ⊎ ∥ Q₆ ⊎ ∥ Q₇ ⊎ ∥ Q₈ ⊎ ∥ Q₉ ⊎ ∥ Q₁₀ ⊎ Q₁₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁
  s₅ = PT.rec squash₁
    (λ { (inl x) → ∣ inl (r₅ x) ∣₁
       ; (inr x) → ∣ inr (s₆ x) ∣₁ })

  s₄ : ∥ P₄ ⊎ ∥ P₅ ⊎ ∥ P₆ ⊎ ∥ P₇ ⊎ ∥ P₈ ⊎ ∥ P₉ ⊎ ∥ P₁₀ ⊎ P₁₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁
     → ∥ Q₄ ⊎ ∥ Q₅ ⊎ ∥ Q₆ ⊎ ∥ Q₇ ⊎ ∥ Q₈ ⊎ ∥ Q₉ ⊎ ∥ Q₁₀ ⊎ Q₁₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁
  s₄ = PT.rec squash₁
    (λ { (inl x) → ∣ inl (r₄ x) ∣₁
       ; (inr x) → ∣ inr (s₅ x) ∣₁ })

  s₃ : ∥ P₃ ⊎ ∥ P₄ ⊎ ∥ P₅ ⊎ ∥ P₆ ⊎ ∥ P₇ ⊎ ∥ P₈ ⊎ ∥ P₉ ⊎ ∥ P₁₀ ⊎ P₁₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁
     → ∥ Q₃ ⊎ ∥ Q₄ ⊎ ∥ Q₅ ⊎ ∥ Q₆ ⊎ ∥ Q₇ ⊎ ∥ Q₈ ⊎ ∥ Q₉ ⊎ ∥ Q₁₀ ⊎ Q₁₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁
  s₃ = PT.rec squash₁
    (λ { (inl x) → ∣ inl (r₃ x) ∣₁
       ; (inr x) → ∣ inr (s₄ x) ∣₁ })

  s₂ : ∥ P₂ ⊎ ∥ P₃ ⊎ ∥ P₄ ⊎ ∥ P₅ ⊎ ∥ P₆ ⊎ ∥ P₇ ⊎ ∥ P₈ ⊎ ∥ P₉ ⊎ ∥ P₁₀ ⊎ P₁₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁
     → ∥ Q₂ ⊎ ∥ Q₃ ⊎ ∥ Q₄ ⊎ ∥ Q₅ ⊎ ∥ Q₆ ⊎ ∥ Q₇ ⊎ ∥ Q₈ ⊎ ∥ Q₉ ⊎ ∥ Q₁₀ ⊎ Q₁₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁
  s₂ = PT.rec squash₁
    (λ { (inl x) → ∣ inl (r₂ x) ∣₁
       ; (inr x) → ∣ inr (s₃ x) ∣₁ })

  s₁ : ∥ P₁ ⊎ ∥ P₂ ⊎ ∥ P₃ ⊎ ∥ P₄ ⊎ ∥ P₅ ⊎ ∥ P₆ ⊎ ∥ P₇ ⊎ ∥ P₈ ⊎ ∥ P₉ ⊎ ∥ P₁₀ ⊎ P₁₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁
     → ∥ Q₁ ⊎ ∥ Q₂ ⊎ ∥ Q₃ ⊎ ∥ Q₄ ⊎ ∥ Q₅ ⊎ ∥ Q₆ ⊎ ∥ Q₇ ⊎ ∥ Q₈ ⊎ ∥ Q₉ ⊎ ∥ Q₁₀ ⊎ Q₁₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁
  s₁ = PT.rec squash₁
    (λ { (inl x) → ∣ inl (r₁ x) ∣₁
       ; (inr x) → ∣ inr (s₂ x) ∣₁ })

  back : ∥ P₀ ⊎ ∥ P₁ ⊎ ∥ P₂ ⊎ ∥ P₃ ⊎ ∥ P₄ ⊎ ∥ P₅ ⊎ ∥ P₆ ⊎ ∥ P₇ ⊎ ∥ P₈ ⊎ ∥ P₉ ⊎ ∥ P₁₀ ⊎ P₁₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁
       → ∥ Q₀ ⊎ ∥ Q₁ ⊎ ∥ Q₂ ⊎ ∥ Q₃ ⊎ ∥ Q₄ ⊎ ∥ Q₅ ⊎ ∥ Q₆ ⊎ ∥ Q₇ ⊎ ∥ Q₈ ⊎ ∥ Q₉ ⊎ ∥ Q₁₀ ⊎ Q₁₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁
  back = PT.rec squash₁
    (λ { (inl x) → ∣ inl (r₀ x) ∣₁
       ; (inr x) → ∣ inr (s₁ x) ∣₁ })

-- =====================================================================
-- SECTION 6. THE WALK, STORY -> MACHINE ONLY, VIA THE KIT.
-- shapesBS A K N0..N11 against shapes A at the (1 + n)-deep frame.
-- The kit's instantiation normalizes each full tree once.
-- =====================================================================
module ShapesAgree {n : ℕ}
  (A K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 : Fin n)
  (γ : S ^ (1 + n))
  (tagEq0 : fst (lookup (suc N0) γ) ≡ fst (numeralL 0))
  (tagEq1 : fst (lookup (suc N1) γ) ≡ fst (numeralL 1))
  (tagEq2 : fst (lookup (suc N2) γ) ≡ fst (numeralL 2))
  (tagEq3 : fst (lookup (suc N3) γ) ≡ fst (numeralL 3))
  (tagEq4 : fst (lookup (suc N4) γ) ≡ fst (numeralL 4))
  (tagEq5 : fst (lookup (suc N5) γ) ≡ fst (numeralL 5))
  (tagEq6 : fst (lookup (suc N6) γ) ≡ fst (numeralL 6))
  (tagEq7 : fst (lookup (suc N7) γ) ≡ fst (numeralL 7))
  (tagEq8 : fst (lookup (suc N8) γ) ≡ fst (numeralL 8))
  (tagEq9 : fst (lookup (suc N9) γ) ≡ fst (numeralL 9))
  (tagEq10 : fst (lookup (suc N10) γ) ≡ fst (numeralL 10))
  (tagEq11 : fst (lookup (suc N11) γ) ≡ fst (numeralL 11))
  (numK0 : ⟨ fst (numeralL 0) ∈ fst (lookup (suc K) γ) ⟩)
  (numK1 : ⟨ fst (numeralL 1) ∈ fst (lookup (suc K) γ) ⟩)
  (numK2 : ⟨ fst (numeralL 2) ∈ fst (lookup (suc K) γ) ⟩)
  (numK3 : ⟨ fst (numeralL 3) ∈ fst (lookup (suc K) γ) ⟩)
  (numK4 : ⟨ fst (numeralL 4) ∈ fst (lookup (suc K) γ) ⟩)
  (numK5 : ⟨ fst (numeralL 5) ∈ fst (lookup (suc K) γ) ⟩)
  (numK6 : ⟨ fst (numeralL 6) ∈ fst (lookup (suc K) γ) ⟩)
  (numK7 : ⟨ fst (numeralL 7) ∈ fst (lookup (suc K) γ) ⟩)
  (numK8 : ⟨ fst (numeralL 8) ∈ fst (lookup (suc K) γ) ⟩)
  (numK9 : ⟨ fst (numeralL 9) ∈ fst (lookup (suc K) γ) ⟩)
  (numK10 : ⟨ fst (numeralL 10) ∈ fst (lookup (suc K) γ) ⟩)
  (numK11 : ⟨ fst (numeralL 11) ∈ fst (lookup (suc K) γ) ⟩)
  (innerK : (k : ℕ) (a : S) → ⟨ fst (prʟ (numeralL k) a) ∈ fst (lookup (suc K) γ) ⟩)
  (innerPairK : (k : ℕ) (a b : S) → ⟨ fst (prʟ (numeralL k) (prʟ a b)) ∈ fst (lookup (suc K) γ) ⟩)
  (pairK : (a b : S) → ⟨ fst (prʟ a b) ∈ fst (lookup (suc K) γ) ⟩) where

  module R0 = BothTmRel {n} A K N0 N1 γ tagEq0 tagEq1 numK0 numK1
  module R1 = BothTmRel {n} A K N0 N1 γ tagEq0 tagEq1 numK0 numK1
  module R10 = FstTmRel {n} A K N0 N1 γ tagEq0 tagEq1 numK0 numK1
  module R11 = FstTmRel {n} A K N0 N1 γ tagEq0 tagEq1 numK0 numK1
  module RT = TopBinRel {n} γ
  module RU = TopUnRel {n} γ
  module R6 = ZeroPayRel {n} N0 γ tagEq0
  module R7 = ZeroPayRel {n} N0 γ tagEq0

  module B0 = BinFormAgree {n} N0 K 0 γ tagEq0 numK0 (innerPairK 0) pairK
               (bothTmBS A K N0 N1) (bothTm A) R0.out
  module B1 = BinFormAgree {n} N1 K 1 γ tagEq1 numK1 (innerPairK 1) pairK
               (bothTmBS A K N0 N1) (bothTm A) R1.out
  module B2 = BinFormAgree {n} N2 K 2 γ tagEq2 numK2 (innerPairK 2) pairK
               (⊤̇ {n = 4 + n}) (⊤̇ {n = 4 + n}) RT.out
  module B3 = BinFormAgree {n} N3 K 3 γ tagEq3 numK3 (innerPairK 3) pairK
               (⊤̇ {n = 4 + n}) (⊤̇ {n = 4 + n}) RT.out
  module B4 = BinFormAgree {n} N4 K 4 γ tagEq4 numK4 (innerPairK 4) pairK
               (⊤̇ {n = 4 + n}) (⊤̇ {n = 4 + n}) RT.out
  module U5 = UnFormAgree {n} N5 K 5 γ tagEq5 numK5 (innerK 5)
               (⊤̇ {n = 3 + n}) (⊤̇ {n = 3 + n}) RU.out
  module U6 = UnFormAgree {n} N6 K 6 γ tagEq6 numK6 (innerK 6)
               (var zero ≐ var (suc (suc (suc N0)))) (var zero ≐ con (numeralL 0))
               R6.out
  module U7 = UnFormAgree {n} N7 K 7 γ tagEq7 numK7 (innerK 7)
               (var zero ≐ var (suc (suc (suc N0)))) (var zero ≐ con (numeralL 0))
               R7.out
  module U8 = UnFormAgree {n} N8 K 8 γ tagEq8 numK8 (innerK 8)
               (⊤̇ {n = 3 + n}) (⊤̇ {n = 3 + n}) RU.out
  module U9 = UnFormAgree {n} N9 K 9 γ tagEq9 numK9 (innerK 9)
               (⊤̇ {n = 3 + n}) (⊤̇ {n = 3 + n}) RU.out
  module B10 = BinFormAgree {n} N10 K 10 γ tagEq10 numK10 (innerPairK 10) pairK
                (fstTmBS A K N0 N1) (fstTm A) R10.out
  module B11 = BinFormAgree {n} N11 K 11 γ tagEq11 numK11 (innerPairK 11) pairK
                (fstTmBS A K N0 N1) (fstTm A) R11.out

  module L = Lift12Back {n} γ
    (⟨ γ ⊨ binFormBS N0 K (bothTmBS A K N0 N1) ⟩)
    (⟨ γ ⊨ binFormBS N1 K (bothTmBS A K N0 N1) ⟩)
    (⟨ γ ⊨ binFormBS N2 K (⊤̇ {n = 4 + n}) ⟩)
    (⟨ γ ⊨ binFormBS N3 K (⊤̇ {n = 4 + n}) ⟩)
    (⟨ γ ⊨ binFormBS N4 K (⊤̇ {n = 4 + n}) ⟩)
    (⟨ γ ⊨ unFormBS N5 K (⊤̇ {n = 3 + n}) ⟩)
    (⟨ γ ⊨ unFormBS N6 K (var zero ≐ var (suc (suc (suc N0)))) ⟩)
    (⟨ γ ⊨ unFormBS N7 K (var zero ≐ var (suc (suc (suc N0)))) ⟩)
    (⟨ γ ⊨ unFormBS N8 K (⊤̇ {n = 3 + n}) ⟩)
    (⟨ γ ⊨ unFormBS N9 K (⊤̇ {n = 3 + n}) ⟩)
    (⟨ γ ⊨ binFormBS N10 K (fstTmBS A K N0 N1) ⟩)
    (⟨ γ ⊨ binFormBS N11 K (fstTmBS A K N0 N1) ⟩)
    (⟨ γ ⊨ binForm 0 (bothTm A) ⟩)
    (⟨ γ ⊨ binForm 1 (bothTm A) ⟩)
    (⟨ γ ⊨ binForm 2 noneB ⟩)
    (⟨ γ ⊨ binForm 3 noneB ⟩)
    (⟨ γ ⊨ binForm 4 noneB ⟩)
    (⟨ γ ⊨ unForm 5 noneU ⟩)
    (⟨ γ ⊨ unForm 6 zeroPay ⟩)
    (⟨ γ ⊨ unForm 7 zeroPay ⟩)
    (⟨ γ ⊨ unForm 8 noneU ⟩)
    (⟨ γ ⊨ unForm 9 noneU ⟩)
    (⟨ γ ⊨ binForm 10 (fstTm A) ⟩)
    (⟨ γ ⊨ binForm 11 (fstTm A) ⟩)
    B0.back B1.back B2.back B3.back B4.back U5.back U6.back U7.back
    U8.back U9.back B10.back B11.back

  back : ⟨ γ ⊨ shapesBS A K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 ⟩
       → ⟨ γ ⊨ shapes A ⟩
  back = L.back

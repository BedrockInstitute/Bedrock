{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.57] probe A: the shapedness walk, WitnessAgree, LeafAgree.
--
-- The walk: shapesBS A K N0..N11 against the machine's shapes A at the
-- (1 + m)-deep frame, twelve disjuncts, per-row frame agreements.  The
-- atoms are imported from ProbeLJ156A (BinShapeClosed/UnShapeClosed/
-- TmAgree) and the master (arTagBS/arTagPairBS transferred there), and
-- from ProbeLJ154A (KeyAgree/DefinesAgree).  Every negative is
-- measured.  Untracked probe; never committed.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ157A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

import FOL.Absoluteness
open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _∧̇_; _∨̇_; _⇒̇_; _≐_; _∈̇_; ∃̇_; ∃̇∈; ∀̇∈; ⊤̇ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; #-inj′; pr-inj )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )
open import L.Coding.Model {ℓ}
  using ( prAtL; prAtL-adequate; arityTagAtL; arityTagAtL-adequate
        ; arityTagPairAtL; arityTagPairAtL-adequate; tagAtL; tagAtL-adequate
        ; tagPairAtL; tagPairAtL-adequate
        ; appAt; appAt-adequate; sucAtL; sucAtL-adequate; prʟ; prʟ-fst
        ; binShapeAt; unShapeAt; bothSameAt; oneSameAt; oneSuccAt; succSndAt
        ; closedAt; binShape-out; binShape-in; unShape-out; unShape-in
        ; domAt; inDomAt; inDomAt-adequate; domAt-out; domAt-in )
open import L.Coding.Shape {ℓ}
  using ( isTmAt; shapes; binForm; unForm; bothTm; fstTm; noneB; noneU; zeroPay; shapedAt )
open import L.Coding.Graph {ℓ} lem using ( satGraphAt; twelveAt )
open import L.Coding.CodeSet {ℓ} lem using ( hasWitnessAt; keyArityAtL )
open import L.Coding.Powerset {ℓ} lem using ( isCodeAt; DefBody; DefinesAt; envOneAt )
open import L.Condensation {ℓ} lem using
  ( arTagBS; arTagPairBS; binShapeBS; unShapeBS; bothSameB; oneSameB
  ; oneSuccB; succSndB; closedBS; domB; tagBS; isTmBS; bothTmBS; fstTmBS
  ; binFormBS; unFormBS; shapesBS; shapedBS; hasWitnessBS; isCodeBS
  ; DefBodyB; module SatGraphB )
import ProbeLJ156A
import ProbeLJ154A
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet using ( #_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
import Cubical.Data.Empty as Empty
open import Cubical.Data.Unit using ( Unit; tt )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Foundations.Function using ( _∘_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

module P156 = ProbeLJ156A {ℓ} lem
module P154 = ProbeLJ154A {ℓ} lem

private
  PairIs : V ℓ → V ℓ → Ω
  PairIs a p = (a ≡ p) , setIsSet a p

-- =====================================================================
-- SECTION 1. THE PER-ROW FRAME AGREEMENTS.
-- binFormBS tag K relB against binForm k relM at the walk frame
-- γ : S ^ (1 + n), under the site facts.  out is machine -> story
-- (needs the components-in-K facts and the membership of the frame's
-- code in the code set C); back is story -> machine (strips the
-- bounds).  The arTagPairBS/arTagBS transfers are ProbeLJ156A's
-- BinShapeClosed/UnShapeClosed at the 4-/3-deep body frame.
-- =====================================================================
module BinFormAgree {n : ℕ} (C : S) (tag K : Fin n) (k : ℕ)
  (γ : S ^ (1 + n))
  (tagEq : fst (lookup (suc tag) γ) ≡ fst (numeralL k))
  (numK : ⟨ fst (numeralL k) ∈ fst (lookup (suc K) γ) ⟩)
  (innerK : (a b : S) → ⟨ fst (prʟ (numeralL k) (prʟ a b)) ∈ fst (lookup (suc K) γ) ⟩)
  (pairK : (a b : S) → ⟨ fst (prʟ a b) ∈ fst (lookup (suc K) γ) ⟩)
  (compK : (c N a b : S) → ⟨ fst c ∈ fst C ⟩
          → fst c ≡ pr (fst N) (pr (# k) (pr (fst a) (fst b)))
          → ⟨ fst N ∈ fst (lookup (suc K) γ) ⟩
            × ⟨ fst a ∈ fst (lookup (suc K) γ) ⟩
            × ⟨ fst b ∈ fst (lookup (suc K) γ) ⟩)
  (relB relM : Formula S (4 + n))
  (relOut : (b a N : S) → ⟨ (b ∷ a ∷ N ∷ γ) ⊨ relB ⟩
          → ⟨ (b ∷ a ∷ N ∷ γ) ⊨ relM ⟩)
  (relBack : (b a N : S) → ⟨ (b ∷ a ∷ N ∷ γ) ⊨ relM ⟩
           → ⟨ (b ∷ a ∷ N ∷ γ) ⊨ relB ⟩) where

  out : ⟨ fst (lookup zero γ) ∈ fst C ⟩
      → ⟨ γ ⊨ binForm k relM ⟩
      → ⟨ γ ⊨ binFormBS tag K relB ⟩
  out c∈C h = PT.rec squash₁ go h
    where
    go : Σ[ N ∈ S ] ⟨ (N ∷ γ) ⊨ ∃̇ (∃̇ (arityTagPairAtL
           (suc (suc (suc zero))) (suc (suc zero)) k (suc zero) zero
           ∧̇ relM)) ⟩
       → ⟨ γ ⊨ binFormBS tag K relB ⟩
    go (N , hN) = PT.rec squash₁ go₂ hN
      where
      go₂ : Σ[ a ∈ S ] ⟨ (a ∷ N ∷ γ) ⊨ ∃̇ (arityTagPairAtL
              (suc (suc (suc zero))) (suc (suc zero)) k (suc zero) zero
              ∧̇ relM) ⟩
          → ⟨ γ ⊨ binFormBS tag K relB ⟩
      go₂ (a , ha) = PT.rec squash₁ go₃ ha
        where
        go₃ : Σ[ b ∈ S ] ⟨ (b ∷ a ∷ N ∷ γ) ⊨ arityTagPairAtL
                (suc (suc (suc zero))) (suc (suc zero)) k (suc zero) zero
                ∧̇ relM ⟩
            → ⟨ γ ⊨ binFormBS tag K relB ⟩
        go₃ (b , (hTag , hRel)) =
          ∣ N , ( ks .fst
                , ∣ a , ( ks .snd .fst
                        , ∣ b , ( ks .snd .snd
                                , ( S.in' hTag , relBack b a N hRel ) ) ∣₁ )
                  ∣₁ ) ∣₁
          where
          module S = P156.BinShapeClosed {n} tag K k (b ∷ a ∷ N ∷ γ)
                       tagEq numK innerK pairK
          shape : fst (lookup zero γ)
                ≡ pr (fst N) (pr (# k) (pr (fst a) (fst b)))
          shape = transport (cong fst (arityTagPairAtL-adequate
                    (suc (suc (suc zero))) (suc (suc zero)) k (suc zero) zero
                    (b ∷ a ∷ N ∷ γ))) hTag
          ks : ⟨ fst N ∈ fst (lookup (suc K) γ) ⟩
             × ⟨ fst a ∈ fst (lookup (suc K) γ) ⟩
             × ⟨ fst b ∈ fst (lookup (suc K) γ) ⟩
          ks = compK (lookup zero γ) N a b c∈C shape

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
          module S = P156.BinShapeClosed {n} tag K k (b ∷ a ∷ N ∷ γ)
                       tagEq numK innerK pairK

module UnFormAgree {n : ℕ} (C : S) (tag K : Fin n) (k : ℕ)
  (γ : S ^ (1 + n))
  (tagEq : fst (lookup (suc tag) γ) ≡ fst (numeralL k))
  (numK : ⟨ fst (numeralL k) ∈ fst (lookup (suc K) γ) ⟩)
  (innerK : (a : S) → ⟨ fst (prʟ (numeralL k) a) ∈ fst (lookup (suc K) γ) ⟩)
  (compK : (c N a : S) → ⟨ fst c ∈ fst C ⟩
          → fst c ≡ pr (fst N) (pr (# k) (fst a))
          → ⟨ fst N ∈ fst (lookup (suc K) γ) ⟩
            × ⟨ fst a ∈ fst (lookup (suc K) γ) ⟩)
  (relB relM : Formula S (3 + n))
  (relOut : (a N : S) → ⟨ (a ∷ N ∷ γ) ⊨ relB ⟩
          → ⟨ (a ∷ N ∷ γ) ⊨ relM ⟩)
  (relBack : (a N : S) → ⟨ (a ∷ N ∷ γ) ⊨ relM ⟩
           → ⟨ (a ∷ N ∷ γ) ⊨ relB ⟩) where

  out : ⟨ fst (lookup zero γ) ∈ fst C ⟩
      → ⟨ γ ⊨ unForm k relM ⟩
      → ⟨ γ ⊨ unFormBS tag K relB ⟩
  out c∈C h = PT.rec squash₁ go h
    where
    go : Σ[ N ∈ S ] ⟨ (N ∷ γ) ⊨ ∃̇ (arityTagAtL
           (suc (suc zero)) (suc zero) k zero ∧̇ relM) ⟩
       → ⟨ γ ⊨ unFormBS tag K relB ⟩
    go (N , hN) = PT.rec squash₁ go₂ hN
      where
      go₂ : Σ[ a ∈ S ] ⟨ (a ∷ N ∷ γ) ⊨ arityTagAtL
              (suc (suc zero)) (suc zero) k zero ∧̇ relM ⟩
          → ⟨ γ ⊨ unFormBS tag K relB ⟩
      go₂ (a , (hTag , hRel)) =
        ∣ N , ( ks .fst
              , ∣ a , ( ks .snd , ( S.in' hTag , relBack a N hRel ) ) ∣₁ ) ∣₁
        where
        module S = P156.UnShapeClosed {n} tag K k (a ∷ N ∷ γ)
                     tagEq numK innerK
        shape : fst (lookup zero γ) ≡ pr (fst N) (pr (# k) (fst a))
        shape = transport (cong fst (arityTagAtL-adequate
                  (suc (suc zero)) (suc zero) k zero (a ∷ N ∷ γ))) hTag
        ks : ⟨ fst N ∈ fst (lookup (suc K) γ) ⟩
           × ⟨ fst a ∈ fst (lookup (suc K) γ) ⟩
        ks = compK (lookup zero γ) N a c∈C shape

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
        module S = P156.UnShapeClosed {n} tag K k (a ∷ N ∷ γ)
                     tagEq numK innerK

-- =====================================================================
-- SECTION 2. THE RELATIONS, POINTWISE.
-- Rows 0/1 carry bothTmBS against bothTm; rows 10/11 carry fstTmBS
-- against fstTm; rows 2/3/4/5/8/9 carry top against top; rows 6/7
-- carry the bounded zero-pin (the N0 slot holds the numeral 0) against
-- the machine's constant zero.
-- =====================================================================
module BothTmRel {n : ℕ} (A K N0 N1 : Fin n) (γ : S ^ (1 + n))
  (tagEq0 : fst (lookup (suc N0) γ) ≡ fst (numeralL 0))
  (tagEq1 : fst (lookup (suc N1) γ) ≡ fst (numeralL 1))
  (numK0 : ⟨ fst (numeralL 0) ∈ fst (lookup (suc K) γ) ⟩)
  (numK1 : ⟨ fst (numeralL 1) ∈ fst (lookup (suc K) γ) ⟩)
  (carrierK : (v : S) → ⟨ fst v ∈ fst (lookup (suc A) γ) ⟩
             → ⟨ fst v ∈ fst (lookup (suc K) γ) ⟩)
  (arityK : (N v : S) → ⟨ fst v ∈ fst N ⟩
           → ⟨ fst v ∈ fst (lookup (suc K) γ) ⟩) where

  out : (b a N : S) → ⟨ (b ∷ a ∷ N ∷ γ) ⊨ bothTmBS A K N0 N1 ⟩
                    → ⟨ (b ∷ a ∷ N ∷ γ) ⊨ bothTm A ⟩
  out b a N (h0 , h1) = (B0.out h0 , B1.out h1)
    where
    module B0 = P156.TmAgree {n} (suc zero) A K N0 N1 (b ∷ a ∷ N ∷ γ)
                   tagEq0 tagEq1 numK0 numK1 carrierK (arityK N)
    module B1 = P156.TmAgree {n} zero A K N0 N1 (b ∷ a ∷ N ∷ γ)
                   tagEq0 tagEq1 numK0 numK1 carrierK (arityK N)

  back : (b a N : S) → ⟨ (b ∷ a ∷ N ∷ γ) ⊨ bothTm A ⟩
                     → ⟨ (b ∷ a ∷ N ∷ γ) ⊨ bothTmBS A K N0 N1 ⟩
  back b a N (h0 , h1) = (B0.in' h0 , B1.in' h1)
    where
    module B0 = P156.TmAgree {n} (suc zero) A K N0 N1 (b ∷ a ∷ N ∷ γ)
                   tagEq0 tagEq1 numK0 numK1 carrierK (arityK N)
    module B1 = P156.TmAgree {n} zero A K N0 N1 (b ∷ a ∷ N ∷ γ)
                   tagEq0 tagEq1 numK0 numK1 carrierK (arityK N)

module FstTmRel {n : ℕ} (A K N0 N1 : Fin n) (γ : S ^ (1 + n))
  (tagEq0 : fst (lookup (suc N0) γ) ≡ fst (numeralL 0))
  (tagEq1 : fst (lookup (suc N1) γ) ≡ fst (numeralL 1))
  (numK0 : ⟨ fst (numeralL 0) ∈ fst (lookup (suc K) γ) ⟩)
  (numK1 : ⟨ fst (numeralL 1) ∈ fst (lookup (suc K) γ) ⟩)
  (carrierK : (v : S) → ⟨ fst v ∈ fst (lookup (suc A) γ) ⟩
             → ⟨ fst v ∈ fst (lookup (suc K) γ) ⟩)
  (arityK : (N v : S) → ⟨ fst v ∈ fst N ⟩
           → ⟨ fst v ∈ fst (lookup (suc K) γ) ⟩) where

  out : (b a N : S) → ⟨ (b ∷ a ∷ N ∷ γ) ⊨ fstTmBS A K N0 N1 ⟩
                    → ⟨ (b ∷ a ∷ N ∷ γ) ⊨ fstTm A ⟩
  out b a N = B.out
    where
    module B = P156.TmAgree {n} (suc zero) A K N0 N1 (b ∷ a ∷ N ∷ γ)
                  tagEq0 tagEq1 numK0 numK1 carrierK (arityK N)

  back : (b a N : S) → ⟨ (b ∷ a ∷ N ∷ γ) ⊨ fstTm A ⟩
                     → ⟨ (b ∷ a ∷ N ∷ γ) ⊨ fstTmBS A K N0 N1 ⟩
  back b a N = B.in'
    where
    module B = P156.TmAgree {n} (suc zero) A K N0 N1 (b ∷ a ∷ N ∷ γ)
                  tagEq0 tagEq1 numK0 numK1 carrierK (arityK N)

module TopBinRel {n : ℕ} (γ : S ^ (1 + n)) where
  out : (b a N : S) → ⟨ (b ∷ a ∷ N ∷ γ) ⊨ ⊤̇ {n = 4 + n} ⟩
                    → ⟨ (b ∷ a ∷ N ∷ γ) ⊨ ⊤̇ {n = 4 + n} ⟩
  out b a N h = h

  back : (b a N : S) → ⟨ (b ∷ a ∷ N ∷ γ) ⊨ ⊤̇ {n = 4 + n} ⟩
                     → ⟨ (b ∷ a ∷ N ∷ γ) ⊨ ⊤̇ {n = 4 + n} ⟩
  back b a N h = h

module TopUnRel {n : ℕ} (γ : S ^ (1 + n)) where
  out : (a N : S) → ⟨ (a ∷ N ∷ γ) ⊨ ⊤̇ {n = 3 + n} ⟩
                  → ⟨ (a ∷ N ∷ γ) ⊨ ⊤̇ {n = 3 + n} ⟩
  out a N h = h

  back : (a N : S) → ⟨ (a ∷ N ∷ γ) ⊨ ⊤̇ {n = 3 + n} ⟩
                   → ⟨ (a ∷ N ∷ γ) ⊨ ⊤̇ {n = 3 + n} ⟩
  back a N h = h

module ZeroPayRel {n : ℕ} (N0 : Fin n) (γ : S ^ (1 + n))
  (tagEq0 : fst (lookup (suc N0) γ) ≡ fst (numeralL 0)) where

  out : (a N : S) → ⟨ (a ∷ N ∷ γ) ⊨ (var zero ≐ var (suc (suc (suc N0)))) ⟩
                  → ⟨ (a ∷ N ∷ γ) ⊨ (var zero ≐ con (numeralL 0)) ⟩
  out a N h = h ∙ tagEq0

  back : (a N : S) → ⟨ (a ∷ N ∷ γ) ⊨ (var zero ≐ con (numeralL 0)) ⟩
                   → ⟨ (a ∷ N ∷ γ) ⊨ (var zero ≐ var (suc (suc (suc N0)))) ⟩
  back a N h = h ∙ sym tagEq0

-- =====================================================================
-- SECTION 3. THE TWELVE-ROW WALK.
-- shapesBS A K N0..N11 against shapes A at the (1 + n)-deep frame,
-- both directions, pointwise under the membership of the frame's code
-- in the code set C (a value parameter; the frame has no code-set
-- slot).  Each row instantiates the frame agreement of section 1.
-- =====================================================================
module ShapesAgree {n : ℕ} (C : S)
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
  (pairK : (a b : S) → ⟨ fst (prʟ a b) ∈ fst (lookup (suc K) γ) ⟩)
  (carrierK : (v : S) → ⟨ fst v ∈ fst (lookup (suc A) γ) ⟩
             → ⟨ fst v ∈ fst (lookup (suc K) γ) ⟩)
  (arityK : (N v : S) → ⟨ fst v ∈ fst N ⟩
           → ⟨ fst v ∈ fst (lookup (suc K) γ) ⟩)
  (compK : (k : ℕ) (c N a b : S) → ⟨ fst c ∈ fst C ⟩
          → fst c ≡ pr (fst N) (pr (# k) (pr (fst a) (fst b)))
          → ⟨ fst N ∈ fst (lookup (suc K) γ) ⟩
            × ⟨ fst a ∈ fst (lookup (suc K) γ) ⟩
            × ⟨ fst b ∈ fst (lookup (suc K) γ) ⟩)
  (unCompK : (k : ℕ) (c N a : S) → ⟨ fst c ∈ fst C ⟩
            → fst c ≡ pr (fst N) (pr (# k) (fst a))
            → ⟨ fst N ∈ fst (lookup (suc K) γ) ⟩
              × ⟨ fst a ∈ fst (lookup (suc K) γ) ⟩) where

  module R0 = BothTmRel {n} A K N0 N1 γ tagEq0 tagEq1 numK0 numK1 carrierK arityK
  module R1 = BothTmRel {n} A K N0 N1 γ tagEq0 tagEq1 numK0 numK1 carrierK arityK
  module R10 = FstTmRel {n} A K N0 N1 γ tagEq0 tagEq1 numK0 numK1 carrierK arityK
  module R11 = FstTmRel {n} A K N0 N1 γ tagEq0 tagEq1 numK0 numK1 carrierK arityK
  module RT = TopBinRel {n} γ
  module RU = TopUnRel {n} γ
  module R6 = ZeroPayRel {n} N0 γ tagEq0
  module R7 = ZeroPayRel {n} N0 γ tagEq0

  module B0 = BinFormAgree {n} C N0 K 0 γ tagEq0 numK0 (innerPairK 0) pairK (compK 0)
               (bothTmBS A K N0 N1) (bothTm A) R0.out R0.back
  module B1 = BinFormAgree {n} C N1 K 1 γ tagEq1 numK1 (innerPairK 1) pairK (compK 1)
               (bothTmBS A K N0 N1) (bothTm A) R1.out R1.back
  module B2 = BinFormAgree {n} C N2 K 2 γ tagEq2 numK2 (innerPairK 2) pairK (compK 2)
               (⊤̇ {n = 4 + n}) (⊤̇ {n = 4 + n}) RT.out RT.back
  module B3 = BinFormAgree {n} C N3 K 3 γ tagEq3 numK3 (innerPairK 3) pairK (compK 3)
               (⊤̇ {n = 4 + n}) (⊤̇ {n = 4 + n}) RT.out RT.back
  module B4 = BinFormAgree {n} C N4 K 4 γ tagEq4 numK4 (innerPairK 4) pairK (compK 4)
               (⊤̇ {n = 4 + n}) (⊤̇ {n = 4 + n}) RT.out RT.back
  module U5 = UnFormAgree {n} C N5 K 5 γ tagEq5 numK5 (innerK 5) (unCompK 5)
               (⊤̇ {n = 3 + n}) (⊤̇ {n = 3 + n}) RU.out RU.back
  module U6 = UnFormAgree {n} C N6 K 6 γ tagEq6 numK6 (innerK 6) (unCompK 6)
               (var zero ≐ var (suc (suc (suc N0)))) (var zero ≐ con (numeralL 0))
               R6.out R6.back
  module U7 = UnFormAgree {n} C N7 K 7 γ tagEq7 numK7 (innerK 7) (unCompK 7)
               (var zero ≐ var (suc (suc (suc N0)))) (var zero ≐ con (numeralL 0))
               R7.out R7.back
  module U8 = UnFormAgree {n} C N8 K 8 γ tagEq8 numK8 (innerK 8) (unCompK 8)
               (⊤̇ {n = 3 + n}) (⊤̇ {n = 3 + n}) RU.out RU.back
  module U9 = UnFormAgree {n} C N9 K 9 γ tagEq9 numK9 (innerK 9) (unCompK 9)
               (⊤̇ {n = 3 + n}) (⊤̇ {n = 3 + n}) RU.out RU.back
  module B10 = BinFormAgree {n} C N10 K 10 γ tagEq10 numK10 (innerPairK 10) pairK (compK 10)
                (fstTmBS A K N0 N1) (fstTm A) R10.out R10.back
  module B11 = BinFormAgree {n} C N11 K 11 γ tagEq11 numK11 (innerPairK 11) pairK (compK 11)
                (fstTmBS A K N0 N1) (fstTm A) R11.out R11.back

  out : ⟨ fst (lookup zero γ) ∈ fst C ⟩
      → ⟨ γ ⊨ shapes A ⟩
      → ⟨ γ ⊨ shapesBS A K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 ⟩
  out c∈C h = o1 c∈C h
    where
    o11 : ⟨ fst (lookup zero γ) ∈ fst C ⟩
        → ⟨ γ ⊨ binForm 10 (fstTm A) ∨̇ binForm 11 (fstTm A) ⟩
        → ⟨ γ ⊨ binFormBS N10 K (fstTmBS A K N0 N1)
             ∨̇ binFormBS N11 K (fstTmBS A K N0 N1) ⟩
    o11 c∈C = PT.rec squash₁
      (λ { (inl x) → ∣ inl (B10.out c∈C x) ∣₁
         ; (inr x) → ∣ inr (B11.out c∈C x) ∣₁ })
    o10 : ⟨ fst (lookup zero γ) ∈ fst C ⟩
        → ⟨ γ ⊨ unForm 9 noneU ∨̇ (binForm 10 (fstTm A) ∨̇ binForm 11 (fstTm A)) ⟩
        → ⟨ γ ⊨ unFormBS N9 K (⊤̇ {n = 3 + n})
             ∨̇ (binFormBS N10 K (fstTmBS A K N0 N1)
               ∨̇ binFormBS N11 K (fstTmBS A K N0 N1)) ⟩
    o10 c∈C = PT.rec squash₁
      (λ { (inl x) → ∣ inl (U9.out c∈C x) ∣₁
         ; (inr x) → ∣ inr (o11 c∈C x) ∣₁ })
    o9 : ⟨ fst (lookup zero γ) ∈ fst C ⟩
       → ⟨ γ ⊨ unForm 8 noneU ∨̇ (unForm 9 noneU ∨̇ (binForm 10 (fstTm A) ∨̇ binForm 11 (fstTm A))) ⟩
       → ⟨ γ ⊨ unFormBS N8 K (⊤̇ {n = 3 + n})
            ∨̇ (unFormBS N9 K (⊤̇ {n = 3 + n})
              ∨̇ (binFormBS N10 K (fstTmBS A K N0 N1)
                ∨̇ binFormBS N11 K (fstTmBS A K N0 N1))) ⟩
    o9 c∈C = PT.rec squash₁
      (λ { (inl x) → ∣ inl (U8.out c∈C x) ∣₁
         ; (inr x) → ∣ inr (o10 c∈C x) ∣₁ })
    o8 : ⟨ fst (lookup zero γ) ∈ fst C ⟩
       → ⟨ γ ⊨ unForm 7 zeroPay ∨̇ (unForm 8 noneU ∨̇ (unForm 9 noneU ∨̇ (binForm 10 (fstTm A) ∨̇ binForm 11 (fstTm A)))) ⟩
       → ⟨ γ ⊨ unFormBS N7 K (var zero ≐ var (suc (suc (suc N0))))
            ∨̇ (unFormBS N8 K (⊤̇ {n = 3 + n})
              ∨̇ (unFormBS N9 K (⊤̇ {n = 3 + n})
                ∨̇ (binFormBS N10 K (fstTmBS A K N0 N1)
                  ∨̇ binFormBS N11 K (fstTmBS A K N0 N1)))) ⟩
    o8 c∈C = PT.rec squash₁
      (λ { (inl x) → ∣ inl (U7.out c∈C x) ∣₁
         ; (inr x) → ∣ inr (o9 c∈C x) ∣₁ })
    o7 : ⟨ fst (lookup zero γ) ∈ fst C ⟩
       → ⟨ γ ⊨ unForm 6 zeroPay ∨̇ (unForm 7 zeroPay ∨̇ (unForm 8 noneU ∨̇ (unForm 9 noneU ∨̇ (binForm 10 (fstTm A) ∨̇ binForm 11 (fstTm A))))) ⟩
       → ⟨ γ ⊨ unFormBS N6 K (var zero ≐ var (suc (suc (suc N0))))
            ∨̇ (unFormBS N7 K (var zero ≐ var (suc (suc (suc N0))))
              ∨̇ (unFormBS N8 K (⊤̇ {n = 3 + n})
                ∨̇ (unFormBS N9 K (⊤̇ {n = 3 + n})
                  ∨̇ (binFormBS N10 K (fstTmBS A K N0 N1)
                    ∨̇ binFormBS N11 K (fstTmBS A K N0 N1))))) ⟩
    o7 c∈C = PT.rec squash₁
      (λ { (inl x) → ∣ inl (U6.out c∈C x) ∣₁
         ; (inr x) → ∣ inr (o8 c∈C x) ∣₁ })
    o6 : ⟨ fst (lookup zero γ) ∈ fst C ⟩
       → ⟨ γ ⊨ unForm 5 noneU ∨̇ (unForm 6 zeroPay ∨̇ (unForm 7 zeroPay ∨̇ (unForm 8 noneU ∨̇ (unForm 9 noneU ∨̇ (binForm 10 (fstTm A) ∨̇ binForm 11 (fstTm A)))))) ⟩
       → ⟨ γ ⊨ unFormBS N5 K (⊤̇ {n = 3 + n})
            ∨̇ (unFormBS N6 K (var zero ≐ var (suc (suc (suc N0))))
              ∨̇ (unFormBS N7 K (var zero ≐ var (suc (suc (suc N0))))
                ∨̇ (unFormBS N8 K (⊤̇ {n = 3 + n})
                  ∨̇ (unFormBS N9 K (⊤̇ {n = 3 + n})
                    ∨̇ (binFormBS N10 K (fstTmBS A K N0 N1)
                      ∨̇ binFormBS N11 K (fstTmBS A K N0 N1)))))) ⟩
    o6 c∈C = PT.rec squash₁
      (λ { (inl x) → ∣ inl (U5.out c∈C x) ∣₁
         ; (inr x) → ∣ inr (o7 c∈C x) ∣₁ })
    o5 : ⟨ fst (lookup zero γ) ∈ fst C ⟩
       → ⟨ γ ⊨ binForm 4 noneB ∨̇ (unForm 5 noneU ∨̇ (unForm 6 zeroPay ∨̇ (unForm 7 zeroPay ∨̇ (unForm 8 noneU ∨̇ (unForm 9 noneU ∨̇ (binForm 10 (fstTm A) ∨̇ binForm 11 (fstTm A))))))) ⟩
       → ⟨ γ ⊨ binFormBS N4 K (⊤̇ {n = 4 + n})
            ∨̇ (unFormBS N5 K (⊤̇ {n = 3 + n})
              ∨̇ (unFormBS N6 K (var zero ≐ var (suc (suc (suc N0))))
                ∨̇ (unFormBS N7 K (var zero ≐ var (suc (suc (suc N0))))
                  ∨̇ (unFormBS N8 K (⊤̇ {n = 3 + n})
                    ∨̇ (unFormBS N9 K (⊤̇ {n = 3 + n})
                      ∨̇ (binFormBS N10 K (fstTmBS A K N0 N1)
                        ∨̇ binFormBS N11 K (fstTmBS A K N0 N1))))))) ⟩
    o5 c∈C = PT.rec squash₁
      (λ { (inl x) → ∣ inl (B4.out c∈C x) ∣₁
         ; (inr x) → ∣ inr (o6 c∈C x) ∣₁ })
    o4 : ⟨ fst (lookup zero γ) ∈ fst C ⟩
       → ⟨ γ ⊨ binForm 3 noneB ∨̇ (binForm 4 noneB ∨̇ (unForm 5 noneU ∨̇ (unForm 6 zeroPay ∨̇ (unForm 7 zeroPay ∨̇ (unForm 8 noneU ∨̇ (unForm 9 noneU ∨̇ (binForm 10 (fstTm A) ∨̇ binForm 11 (fstTm A)))))))) ⟩
       → ⟨ γ ⊨ binFormBS N3 K (⊤̇ {n = 4 + n})
            ∨̇ (binFormBS N4 K (⊤̇ {n = 4 + n})
              ∨̇ (unFormBS N5 K (⊤̇ {n = 3 + n})
                ∨̇ (unFormBS N6 K (var zero ≐ var (suc (suc (suc N0))))
                  ∨̇ (unFormBS N7 K (var zero ≐ var (suc (suc (suc N0))))
                    ∨̇ (unFormBS N8 K (⊤̇ {n = 3 + n})
                      ∨̇ (unFormBS N9 K (⊤̇ {n = 3 + n})
                        ∨̇ (binFormBS N10 K (fstTmBS A K N0 N1)
                          ∨̇ binFormBS N11 K (fstTmBS A K N0 N1)))))))) ⟩
    o4 c∈C = PT.rec squash₁
      (λ { (inl x) → ∣ inl (B3.out c∈C x) ∣₁
         ; (inr x) → ∣ inr (o5 c∈C x) ∣₁ })
    o3 : ⟨ fst (lookup zero γ) ∈ fst C ⟩
       → ⟨ γ ⊨ binForm 2 noneB ∨̇ (binForm 3 noneB ∨̇ (binForm 4 noneB ∨̇ (unForm 5 noneU ∨̇ (unForm 6 zeroPay ∨̇ (unForm 7 zeroPay ∨̇ (unForm 8 noneU ∨̇ (unForm 9 noneU ∨̇ (binForm 10 (fstTm A) ∨̇ binForm 11 (fstTm A))))))))) ⟩
       → ⟨ γ ⊨ binFormBS N2 K (⊤̇ {n = 4 + n})
            ∨̇ (binFormBS N3 K (⊤̇ {n = 4 + n})
              ∨̇ (binFormBS N4 K (⊤̇ {n = 4 + n})
                ∨̇ (unFormBS N5 K (⊤̇ {n = 3 + n})
                  ∨̇ (unFormBS N6 K (var zero ≐ var (suc (suc (suc N0))))
                    ∨̇ (unFormBS N7 K (var zero ≐ var (suc (suc (suc N0))))
                      ∨̇ (unFormBS N8 K (⊤̇ {n = 3 + n})
                        ∨̇ (unFormBS N9 K (⊤̇ {n = 3 + n})
                          ∨̇ (binFormBS N10 K (fstTmBS A K N0 N1)
                            ∨̇ binFormBS N11 K (fstTmBS A K N0 N1))))))))) ⟩
    o3 c∈C = PT.rec squash₁
      (λ { (inl x) → ∣ inl (B2.out c∈C x) ∣₁
         ; (inr x) → ∣ inr (o4 c∈C x) ∣₁ })
    o2 : ⟨ fst (lookup zero γ) ∈ fst C ⟩
       → ⟨ γ ⊨ binForm 1 (bothTm A) ∨̇ (binForm 2 noneB ∨̇ (binForm 3 noneB ∨̇ (binForm 4 noneB ∨̇ (unForm 5 noneU ∨̇ (unForm 6 zeroPay ∨̇ (unForm 7 zeroPay ∨̇ (unForm 8 noneU ∨̇ (unForm 9 noneU ∨̇ (binForm 10 (fstTm A) ∨̇ binForm 11 (fstTm A)))))))))) ⟩
       → ⟨ γ ⊨ binFormBS N1 K (bothTmBS A K N0 N1)
            ∨̇ (binFormBS N2 K (⊤̇ {n = 4 + n})
              ∨̇ (binFormBS N3 K (⊤̇ {n = 4 + n})
                ∨̇ (binFormBS N4 K (⊤̇ {n = 4 + n})
                  ∨̇ (unFormBS N5 K (⊤̇ {n = 3 + n})
                    ∨̇ (unFormBS N6 K (var zero ≐ var (suc (suc (suc N0))))
                      ∨̇ (unFormBS N7 K (var zero ≐ var (suc (suc (suc N0))))
                        ∨̇ (unFormBS N8 K (⊤̇ {n = 3 + n})
                          ∨̇ (unFormBS N9 K (⊤̇ {n = 3 + n})
                            ∨̇ (binFormBS N10 K (fstTmBS A K N0 N1)
                              ∨̇ binFormBS N11 K (fstTmBS A K N0 N1)))))))))) ⟩
    o2 c∈C = PT.rec squash₁
      (λ { (inl x) → ∣ inl (B1.out c∈C x) ∣₁
         ; (inr x) → ∣ inr (o3 c∈C x) ∣₁ })
    o1 : ⟨ fst (lookup zero γ) ∈ fst C ⟩
       → ⟨ γ ⊨ shapes A ⟩
       → ⟨ γ ⊨ shapesBS A K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 ⟩
    o1 c∈C = PT.rec squash₁
      (λ { (inl x) → ∣ inl (B0.out c∈C x) ∣₁
         ; (inr x) → ∣ inr (o2 c∈C x) ∣₁ })

  back : ⟨ fst (lookup zero γ) ∈ fst C ⟩
       → ⟨ γ ⊨ shapesBS A K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 ⟩
       → ⟨ γ ⊨ shapes A ⟩
  back c∈C h = b1 c∈C h
    where
    b11 : ⟨ fst (lookup zero γ) ∈ fst C ⟩
        → ⟨ γ ⊨ binFormBS N10 K (fstTmBS A K N0 N1)
             ∨̇ binFormBS N11 K (fstTmBS A K N0 N1) ⟩
        → ⟨ γ ⊨ binForm 10 (fstTm A) ∨̇ binForm 11 (fstTm A) ⟩
    b11 c∈C = PT.rec squash₁
      (λ { (inl x) → ∣ inl (B10.back x) ∣₁
         ; (inr x) → ∣ inr (B11.back x) ∣₁ })
    b10 : ⟨ fst (lookup zero γ) ∈ fst C ⟩
        → ⟨ γ ⊨ unFormBS N9 K (⊤̇ {n = 3 + n})
             ∨̇ (binFormBS N10 K (fstTmBS A K N0 N1)
               ∨̇ binFormBS N11 K (fstTmBS A K N0 N1)) ⟩
        → ⟨ γ ⊨ unForm 9 noneU ∨̇ (binForm 10 (fstTm A) ∨̇ binForm 11 (fstTm A)) ⟩
    b10 c∈C = PT.rec squash₁
      (λ { (inl x) → ∣ inl (U9.back x) ∣₁
         ; (inr x) → ∣ inr (b11 c∈C x) ∣₁ })
    b9 : ⟨ fst (lookup zero γ) ∈ fst C ⟩
       → ⟨ γ ⊨ unFormBS N8 K (⊤̇ {n = 3 + n})
            ∨̇ (unFormBS N9 K (⊤̇ {n = 3 + n})
              ∨̇ (binFormBS N10 K (fstTmBS A K N0 N1)
                ∨̇ binFormBS N11 K (fstTmBS A K N0 N1))) ⟩
       → ⟨ γ ⊨ unForm 8 noneU ∨̇ (unForm 9 noneU ∨̇ (binForm 10 (fstTm A) ∨̇ binForm 11 (fstTm A))) ⟩
    b9 c∈C = PT.rec squash₁
      (λ { (inl x) → ∣ inl (U8.back x) ∣₁
         ; (inr x) → ∣ inr (b10 c∈C x) ∣₁ })
    b8 : ⟨ fst (lookup zero γ) ∈ fst C ⟩
       → ⟨ γ ⊨ unFormBS N7 K (var zero ≐ var (suc (suc (suc N0))))
            ∨̇ (unFormBS N8 K (⊤̇ {n = 3 + n})
              ∨̇ (unFormBS N9 K (⊤̇ {n = 3 + n})
                ∨̇ (binFormBS N10 K (fstTmBS A K N0 N1)
                  ∨̇ binFormBS N11 K (fstTmBS A K N0 N1)))) ⟩
       → ⟨ γ ⊨ unForm 7 zeroPay ∨̇ (unForm 8 noneU ∨̇ (unForm 9 noneU ∨̇ (binForm 10 (fstTm A) ∨̇ binForm 11 (fstTm A)))) ⟩
    b8 c∈C = PT.rec squash₁
      (λ { (inl x) → ∣ inl (U7.back x) ∣₁
         ; (inr x) → ∣ inr (b9 c∈C x) ∣₁ })
    b7 : ⟨ fst (lookup zero γ) ∈ fst C ⟩
       → ⟨ γ ⊨ unFormBS N6 K (var zero ≐ var (suc (suc (suc N0))))
            ∨̇ (unFormBS N7 K (var zero ≐ var (suc (suc (suc N0))))
              ∨̇ (unFormBS N8 K (⊤̇ {n = 3 + n})
                ∨̇ (unFormBS N9 K (⊤̇ {n = 3 + n})
                  ∨̇ (binFormBS N10 K (fstTmBS A K N0 N1)
                    ∨̇ binFormBS N11 K (fstTmBS A K N0 N1))))) ⟩
       → ⟨ γ ⊨ unForm 6 zeroPay ∨̇ (unForm 7 zeroPay ∨̇ (unForm 8 noneU ∨̇ (unForm 9 noneU ∨̇ (binForm 10 (fstTm A) ∨̇ binForm 11 (fstTm A))))) ⟩
    b7 c∈C = PT.rec squash₁
      (λ { (inl x) → ∣ inl (U6.back x) ∣₁
         ; (inr x) → ∣ inr (b8 c∈C x) ∣₁ })
    b6 : ⟨ fst (lookup zero γ) ∈ fst C ⟩
       → ⟨ γ ⊨ unFormBS N5 K (⊤̇ {n = 3 + n})
            ∨̇ (unFormBS N6 K (var zero ≐ var (suc (suc (suc N0))))
              ∨̇ (unFormBS N7 K (var zero ≐ var (suc (suc (suc N0))))
                ∨̇ (unFormBS N8 K (⊤̇ {n = 3 + n})
                  ∨̇ (unFormBS N9 K (⊤̇ {n = 3 + n})
                    ∨̇ (binFormBS N10 K (fstTmBS A K N0 N1)
                      ∨̇ binFormBS N11 K (fstTmBS A K N0 N1)))))) ⟩
       → ⟨ γ ⊨ unForm 5 noneU ∨̇ (unForm 6 zeroPay ∨̇ (unForm 7 zeroPay ∨̇ (unForm 8 noneU ∨̇ (unForm 9 noneU ∨̇ (binForm 10 (fstTm A) ∨̇ binForm 11 (fstTm A)))))) ⟩
    b6 c∈C = PT.rec squash₁
      (λ { (inl x) → ∣ inl (U5.back x) ∣₁
         ; (inr x) → ∣ inr (b7 c∈C x) ∣₁ })
    b5 : ⟨ fst (lookup zero γ) ∈ fst C ⟩
       → ⟨ γ ⊨ binFormBS N4 K (⊤̇ {n = 4 + n})
            ∨̇ (unFormBS N5 K (⊤̇ {n = 3 + n})
              ∨̇ (unFormBS N6 K (var zero ≐ var (suc (suc (suc N0))))
                ∨̇ (unFormBS N7 K (var zero ≐ var (suc (suc (suc N0))))
                  ∨̇ (unFormBS N8 K (⊤̇ {n = 3 + n})
                    ∨̇ (unFormBS N9 K (⊤̇ {n = 3 + n})
                      ∨̇ (binFormBS N10 K (fstTmBS A K N0 N1)
                        ∨̇ binFormBS N11 K (fstTmBS A K N0 N1))))))) ⟩
       → ⟨ γ ⊨ binForm 4 noneB ∨̇ (unForm 5 noneU ∨̇ (unForm 6 zeroPay ∨̇ (unForm 7 zeroPay ∨̇ (unForm 8 noneU ∨̇ (unForm 9 noneU ∨̇ (binForm 10 (fstTm A) ∨̇ binForm 11 (fstTm A))))))) ⟩
    b5 c∈C = PT.rec squash₁
      (λ { (inl x) → ∣ inl (B4.back x) ∣₁
         ; (inr x) → ∣ inr (b6 c∈C x) ∣₁ })
    b4 : ⟨ fst (lookup zero γ) ∈ fst C ⟩
       → ⟨ γ ⊨ binFormBS N3 K (⊤̇ {n = 4 + n})
            ∨̇ (binFormBS N4 K (⊤̇ {n = 4 + n})
              ∨̇ (unFormBS N5 K (⊤̇ {n = 3 + n})
                ∨̇ (unFormBS N6 K (var zero ≐ var (suc (suc (suc N0))))
                  ∨̇ (unFormBS N7 K (var zero ≐ var (suc (suc (suc N0))))
                    ∨̇ (unFormBS N8 K (⊤̇ {n = 3 + n})
                      ∨̇ (unFormBS N9 K (⊤̇ {n = 3 + n})
                        ∨̇ (binFormBS N10 K (fstTmBS A K N0 N1)
                          ∨̇ binFormBS N11 K (fstTmBS A K N0 N1)))))))) ⟩
       → ⟨ γ ⊨ binForm 3 noneB ∨̇ (binForm 4 noneB ∨̇ (unForm 5 noneU ∨̇ (unForm 6 zeroPay ∨̇ (unForm 7 zeroPay ∨̇ (unForm 8 noneU ∨̇ (unForm 9 noneU ∨̇ (binForm 10 (fstTm A) ∨̇ binForm 11 (fstTm A)))))))) ⟩
    b4 c∈C = PT.rec squash₁
      (λ { (inl x) → ∣ inl (B3.back x) ∣₁
         ; (inr x) → ∣ inr (b5 c∈C x) ∣₁ })
    b3 : ⟨ fst (lookup zero γ) ∈ fst C ⟩
       → ⟨ γ ⊨ binFormBS N2 K (⊤̇ {n = 4 + n})
            ∨̇ (binFormBS N3 K (⊤̇ {n = 4 + n})
              ∨̇ (binFormBS N4 K (⊤̇ {n = 4 + n})
                ∨̇ (unFormBS N5 K (⊤̇ {n = 3 + n})
                  ∨̇ (unFormBS N6 K (var zero ≐ var (suc (suc (suc N0))))
                    ∨̇ (unFormBS N7 K (var zero ≐ var (suc (suc (suc N0))))
                      ∨̇ (unFormBS N8 K (⊤̇ {n = 3 + n})
                        ∨̇ (unFormBS N9 K (⊤̇ {n = 3 + n})
                          ∨̇ (binFormBS N10 K (fstTmBS A K N0 N1)
                            ∨̇ binFormBS N11 K (fstTmBS A K N0 N1))))))))) ⟩
       → ⟨ γ ⊨ binForm 2 noneB ∨̇ (binForm 3 noneB ∨̇ (binForm 4 noneB ∨̇ (unForm 5 noneU ∨̇ (unForm 6 zeroPay ∨̇ (unForm 7 zeroPay ∨̇ (unForm 8 noneU ∨̇ (unForm 9 noneU ∨̇ (binForm 10 (fstTm A) ∨̇ binForm 11 (fstTm A))))))))) ⟩
    b3 c∈C = PT.rec squash₁
      (λ { (inl x) → ∣ inl (B2.back x) ∣₁
         ; (inr x) → ∣ inr (b4 c∈C x) ∣₁ })
    b2 : ⟨ fst (lookup zero γ) ∈ fst C ⟩
       → ⟨ γ ⊨ binFormBS N1 K (bothTmBS A K N0 N1)
            ∨̇ (binFormBS N2 K (⊤̇ {n = 4 + n})
              ∨̇ (binFormBS N3 K (⊤̇ {n = 4 + n})
                ∨̇ (binFormBS N4 K (⊤̇ {n = 4 + n})
                  ∨̇ (unFormBS N5 K (⊤̇ {n = 3 + n})
                    ∨̇ (unFormBS N6 K (var zero ≐ var (suc (suc (suc N0))))
                      ∨̇ (unFormBS N7 K (var zero ≐ var (suc (suc (suc N0))))
                        ∨̇ (unFormBS N8 K (⊤̇ {n = 3 + n})
                          ∨̇ (unFormBS N9 K (⊤̇ {n = 3 + n})
                            ∨̇ (binFormBS N10 K (fstTmBS A K N0 N1)
                              ∨̇ binFormBS N11 K (fstTmBS A K N0 N1)))))))))) ⟩
       → ⟨ γ ⊨ binForm 1 (bothTm A) ∨̇ (binForm 2 noneB ∨̇ (binForm 3 noneB ∨̇ (binForm 4 noneB ∨̇ (unForm 5 noneU ∨̇ (unForm 6 zeroPay ∨̇ (unForm 7 zeroPay ∨̇ (unForm 8 noneU ∨̇ (unForm 9 noneU ∨̇ (binForm 10 (fstTm A) ∨̇ binForm 11 (fstTm A)))))))))) ⟩
    b2 c∈C = PT.rec squash₁
      (λ { (inl x) → ∣ inl (B1.back x) ∣₁
         ; (inr x) → ∣ inr (b3 c∈C x) ∣₁ })
    b1 : ⟨ fst (lookup zero γ) ∈ fst C ⟩
       → ⟨ γ ⊨ shapesBS A K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 ⟩
       → ⟨ γ ⊨ shapes A ⟩
    b1 c∈C = PT.rec squash₁
      (λ { (inl x) → ∣ inl (B0.back x) ∣₁
         ; (inr x) → ∣ inr (b2 c∈C x) ∣₁ })

-- =====================================================================
-- SECTION 4. ShapedAgree AND WitnessAgree.
-- shapedBS C A K Ns against shapedAt C A at the n-deep frame, then
-- hasWitnessBS A x K Ns against hasWitnessAt A x.  The closedness
-- part is ProbeLJ156A's ClosedAgree at the witness frame (C = the
-- witness, K and the tags suc-lifted); the shapedness part is section
-- 3's walk wrapped in the forall-in frame.  The membership facts
-- (codesK, unCodesK, entryK) are functions of the witness, because
-- the witness is bound inside the existential.
-- =====================================================================
module ShapedAgree {n : ℕ} (C A K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 : Fin n)
  (γ : S ^ n)
  (tagEq0 : fst (lookup N0 γ) ≡ fst (numeralL 0))
  (tagEq1 : fst (lookup N1 γ) ≡ fst (numeralL 1))
  (tagEq2 : fst (lookup N2 γ) ≡ fst (numeralL 2))
  (tagEq3 : fst (lookup N3 γ) ≡ fst (numeralL 3))
  (tagEq4 : fst (lookup N4 γ) ≡ fst (numeralL 4))
  (tagEq5 : fst (lookup N5 γ) ≡ fst (numeralL 5))
  (tagEq6 : fst (lookup N6 γ) ≡ fst (numeralL 6))
  (tagEq7 : fst (lookup N7 γ) ≡ fst (numeralL 7))
  (tagEq8 : fst (lookup N8 γ) ≡ fst (numeralL 8))
  (tagEq9 : fst (lookup N9 γ) ≡ fst (numeralL 9))
  (tagEq10 : fst (lookup N10 γ) ≡ fst (numeralL 10))
  (tagEq11 : fst (lookup N11 γ) ≡ fst (numeralL 11))
  (numK0 : ⟨ fst (numeralL 0) ∈ fst (lookup K γ) ⟩)
  (numK1 : ⟨ fst (numeralL 1) ∈ fst (lookup K γ) ⟩)
  (numK2 : ⟨ fst (numeralL 2) ∈ fst (lookup K γ) ⟩)
  (numK3 : ⟨ fst (numeralL 3) ∈ fst (lookup K γ) ⟩)
  (numK4 : ⟨ fst (numeralL 4) ∈ fst (lookup K γ) ⟩)
  (numK5 : ⟨ fst (numeralL 5) ∈ fst (lookup K γ) ⟩)
  (numK6 : ⟨ fst (numeralL 6) ∈ fst (lookup K γ) ⟩)
  (numK7 : ⟨ fst (numeralL 7) ∈ fst (lookup K γ) ⟩)
  (numK8 : ⟨ fst (numeralL 8) ∈ fst (lookup K γ) ⟩)
  (numK9 : ⟨ fst (numeralL 9) ∈ fst (lookup K γ) ⟩)
  (numK10 : ⟨ fst (numeralL 10) ∈ fst (lookup K γ) ⟩)
  (numK11 : ⟨ fst (numeralL 11) ∈ fst (lookup K γ) ⟩)
  (innerK : (k : ℕ) (a : S) → ⟨ fst (prʟ (numeralL k) a) ∈ fst (lookup K γ) ⟩)
  (innerPairK : (k : ℕ) (a b : S) → ⟨ fst (prʟ (numeralL k) (prʟ a b)) ∈ fst (lookup K γ) ⟩)
  (pairK : (a b : S) → ⟨ fst (prʟ a b) ∈ fst (lookup K γ) ⟩)
  (carrierK : (v : S) → ⟨ fst v ∈ fst (lookup A γ) ⟩
             → ⟨ fst v ∈ fst (lookup K γ) ⟩)
  (arityK : (N v : S) → ⟨ fst v ∈ fst N ⟩
           → ⟨ fst v ∈ fst (lookup K γ) ⟩)
  (codesK : (k : ℕ) (c ar a b : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
           → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
           → ⟨ fst ar ∈ fst (lookup K γ) ⟩
             × ⟨ fst a ∈ fst (lookup K γ) ⟩ × ⟨ fst b ∈ fst (lookup K γ) ⟩)
  (unCodesK : (k : ℕ) (c ar a : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
             → fst c ≡ pr (fst ar) (pr (# k) (fst a))
             → ⟨ fst ar ∈ fst (lookup K γ) ⟩ × ⟨ fst a ∈ fst (lookup K γ) ⟩) where

  out : ⟨ γ ⊨ shapedAt C A ⟩ → ⟨ γ ⊨ shapedBS C A K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 ⟩
  out h = λ c c∈ →
    let module S = ShapesAgree {n} (lookup C γ) A K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11
          (c ∷ γ)
          tagEq0 tagEq1 tagEq2 tagEq3 tagEq4 tagEq5 tagEq6 tagEq7 tagEq8 tagEq9 tagEq10 tagEq11
          numK0 numK1 numK2 numK3 numK4 numK5 numK6 numK7 numK8 numK9 numK10 numK11
          innerK innerPairK pairK carrierK arityK codesK unCodesK
    in S.out c∈ (h c c∈)

  back : ⟨ γ ⊨ shapedBS C A K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 ⟩
       → ⟨ γ ⊨ shapedAt C A ⟩
  back h = λ c c∈ →
    let module S = ShapesAgree {n} (lookup C γ) A K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11
          (c ∷ γ)
          tagEq0 tagEq1 tagEq2 tagEq3 tagEq4 tagEq5 tagEq6 tagEq7 tagEq8 tagEq9 tagEq10 tagEq11
          numK0 numK1 numK2 numK3 numK4 numK5 numK6 numK7 numK8 numK9 numK10 numK11
          innerK innerPairK pairK carrierK arityK codesK unCodesK
    in S.back c∈ (h c c∈)

module WitnessAgree {n : ℕ} (A x K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 : Fin n)
  (γ : S ^ n)
  (tagEq0 : fst (lookup N0 γ) ≡ fst (numeralL 0))
  (tagEq1 : fst (lookup N1 γ) ≡ fst (numeralL 1))
  (tagEq2 : fst (lookup N2 γ) ≡ fst (numeralL 2))
  (tagEq3 : fst (lookup N3 γ) ≡ fst (numeralL 3))
  (tagEq4 : fst (lookup N4 γ) ≡ fst (numeralL 4))
  (tagEq5 : fst (lookup N5 γ) ≡ fst (numeralL 5))
  (tagEq6 : fst (lookup N6 γ) ≡ fst (numeralL 6))
  (tagEq7 : fst (lookup N7 γ) ≡ fst (numeralL 7))
  (tagEq8 : fst (lookup N8 γ) ≡ fst (numeralL 8))
  (tagEq9 : fst (lookup N9 γ) ≡ fst (numeralL 9))
  (tagEq10 : fst (lookup N10 γ) ≡ fst (numeralL 10))
  (tagEq11 : fst (lookup N11 γ) ≡ fst (numeralL 11))
  (numK0 : ⟨ fst (numeralL 0) ∈ fst (lookup K γ) ⟩)
  (numK1 : ⟨ fst (numeralL 1) ∈ fst (lookup K γ) ⟩)
  (numK2 : ⟨ fst (numeralL 2) ∈ fst (lookup K γ) ⟩)
  (numK3 : ⟨ fst (numeralL 3) ∈ fst (lookup K γ) ⟩)
  (numK4 : ⟨ fst (numeralL 4) ∈ fst (lookup K γ) ⟩)
  (numK5 : ⟨ fst (numeralL 5) ∈ fst (lookup K γ) ⟩)
  (numK6 : ⟨ fst (numeralL 6) ∈ fst (lookup K γ) ⟩)
  (numK7 : ⟨ fst (numeralL 7) ∈ fst (lookup K γ) ⟩)
  (numK8 : ⟨ fst (numeralL 8) ∈ fst (lookup K γ) ⟩)
  (numK9 : ⟨ fst (numeralL 9) ∈ fst (lookup K γ) ⟩)
  (numK10 : ⟨ fst (numeralL 10) ∈ fst (lookup K γ) ⟩)
  (numK11 : ⟨ fst (numeralL 11) ∈ fst (lookup K γ) ⟩)
  (innerK : (k : ℕ) (a : S) → ⟨ fst (prʟ (numeralL k) a) ∈ fst (lookup K γ) ⟩)
  (innerPairK : (k : ℕ) (a b : S) → ⟨ fst (prʟ (numeralL k) (prʟ a b)) ∈ fst (lookup K γ) ⟩)
  (pairK : (a b : S) → ⟨ fst (prʟ a b) ∈ fst (lookup K γ) ⟩)
  (carrierK : (v : S) → ⟨ fst v ∈ fst (lookup A γ) ⟩
             → ⟨ fst v ∈ fst (lookup K γ) ⟩)
  (arityK : (N v : S) → ⟨ fst v ∈ fst N ⟩
           → ⟨ fst v ∈ fst (lookup K γ) ⟩)
  (witK : (w : S) → ⟨ (w ∷ γ) ⊨ ((var (suc x) ∈̇ var zero)
               ∧̇ (closedAt zero ∧̇ shapedAt zero (suc A))) ⟩
         → ⟨ fst w ∈ fst (lookup K γ) ⟩)
  (codesK : (w : S) → (k : ℕ) → (c ar a b : S) → ⟨ fst c ∈ fst w ⟩
           → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
           → ⟨ fst ar ∈ fst (lookup K γ) ⟩
             × ⟨ fst a ∈ fst (lookup K γ) ⟩ × ⟨ fst b ∈ fst (lookup K γ) ⟩)
  (unCodesK : (w : S) → (k : ℕ) → (c ar a : S) → ⟨ fst c ∈ fst w ⟩
             → fst c ≡ pr (fst ar) (pr (# k) (fst a))
             → ⟨ fst ar ∈ fst (lookup K γ) ⟩ × ⟨ fst a ∈ fst (lookup K γ) ⟩)
  (entryK : (w x' y : S) → ⟨ pr (fst x') (fst y) ∈ fst w ⟩
           → ⟨ fst x' ∈ fst (lookup K γ) ⟩ × ⟨ fst y ∈ fst (lookup K γ) ⟩) where

  out : ⟨ γ ⊨ hasWitnessAt A x ⟩
      → ⟨ γ ⊨ hasWitnessBS A x K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 ⟩
  out h = PT.rec squash₁ go h
    where
    go : Σ[ w ∈ S ] ⟨ (w ∷ γ) ⊨ ((var (suc x) ∈̇ var zero)
           ∧̇ (closedAt zero ∧̇ shapedAt zero (suc A))) ⟩
       → ⟨ γ ⊨ hasWitnessBS A x K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 ⟩
    go (w , (hxw , (hcl , hsh))) =
      ∣ w , ( witK w (hxw , (hcl , hsh))
            , ( hxw , ( CA.out hcl , SA.out hsh ) ) ) ∣₁
      where
      module CA = P156.ClosedAgree {1 + n} zero (suc K)
                    (suc N2) (suc N3) (suc N4) (suc N5)
                    (suc N8) (suc N9) (suc N10) (suc N11) (w ∷ γ)
                    tagEq2 tagEq3 tagEq4 tagEq5 tagEq8 tagEq9 tagEq10 tagEq11
                    numK2 numK3 numK4 numK5 numK8 numK9 numK10 numK11
                    innerK innerPairK pairK (codesK w) (unCodesK w) (entryK w)
      module SA = ShapedAgree {1 + n} zero (suc A) (suc K)
                    (suc N0) (suc N1) (suc N2) (suc N3) (suc N4) (suc N5)
                    (suc N6) (suc N7) (suc N8) (suc N9) (suc N10) (suc N11) (w ∷ γ)
                    tagEq0 tagEq1 tagEq2 tagEq3 tagEq4 tagEq5 tagEq6 tagEq7
                    tagEq8 tagEq9 tagEq10 tagEq11
                    numK0 numK1 numK2 numK3 numK4 numK5 numK6 numK7
                    numK8 numK9 numK10 numK11
                    innerK innerPairK pairK carrierK arityK (codesK w) (unCodesK w)

-- =====================================================================

  back : ⟨ γ ⊨ hasWitnessBS A x K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 ⟩
       → ⟨ γ ⊨ hasWitnessAt A x ⟩
  back h = PT.rec squash₁ go h
    where
    go : Σ[ w ∈ S ] (⟨ fst w ∈ fst (lookup K γ) ⟩
                    × ⟨ (w ∷ γ) ⊨ ((var (suc x) ∈̇ var zero)
                         ∧̇ (closedBS zero (suc K) (suc N2) (suc N3) (suc N4) (suc N5)
                               (suc N8) (suc N9) (suc N10) (suc N11)
                           ∧̇ shapedBS zero (suc A) (suc K)
                                (suc N0) (suc N1) (suc N2) (suc N3) (suc N4) (suc N5)
                                (suc N6) (suc N7) (suc N8) (suc N9) (suc N10) (suc N11))) ⟩)
       → ⟨ γ ⊨ hasWitnessAt A x ⟩
    go (w , (wK , (hxw , (hcl , hsh)))) =
      ∣ w , ( hxw , ( CA.back hcl , SA.back hsh ) ) ∣₁
      where
      module CA = P156.ClosedAgree {1 + n} zero (suc K)
                    (suc N2) (suc N3) (suc N4) (suc N5)
                    (suc N8) (suc N9) (suc N10) (suc N11) (w ∷ γ)
                    tagEq2 tagEq3 tagEq4 tagEq5 tagEq8 tagEq9 tagEq10 tagEq11
                    numK2 numK3 numK4 numK5 numK8 numK9 numK10 numK11
                    innerK innerPairK pairK (codesK w) (unCodesK w) (entryK w)
      module SA = ShapedAgree {1 + n} zero (suc A) (suc K)
                    (suc N0) (suc N1) (suc N2) (suc N3) (suc N4) (suc N5)
                    (suc N6) (suc N7) (suc N8) (suc N9) (suc N10) (suc N11) (w ∷ γ)
                    tagEq0 tagEq1 tagEq2 tagEq3 tagEq4 tagEq5 tagEq6 tagEq7
                    tagEq8 tagEq9 tagEq10 tagEq11
                    numK0 numK1 numK2 numK3 numK4 numK5 numK6 numK7
                    numK8 numK9 numK10 numK11
                    innerK innerPairK pairK carrierK arityK (codesK w) (unCodesK w)
-- SECTION 5. LeafAgree: THE DefBodyB / DefBody LEAF ADEQUACY.
-- At the leaf environment γ : S ^ (8 + n), DefBodyB w K N0..N11 t0 t1
-- against DefBody {5 + n} w, one conjunction deep.  The three leaves:
-- isCodeBS <-> isCodeAt (KeyAgree x WitnessAgree), SatGraphB.satGraphB
-- <-> satGraphAt (ProbeLJ156A's SatGraphAgree, whose twelve-row
-- composition is a parameter), and DefinesBS <-> DefinesAt
-- (ProbeLJ154A's DefinesAgree).  out is machine -> story; back is
-- story -> machine.
-- =====================================================================
module LeafAgree {n : ℕ} (w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 : Fin (5 + n))
  (γ : S ^ (8 + n))
  (tagEq0 : fst (lookup (suc (suc (suc N0))) γ) ≡ fst (numeralL 0))
  (tagEq1 : fst (lookup (suc (suc (suc N1))) γ) ≡ fst (numeralL 1))
  (tagEq2 : fst (lookup (suc (suc (suc N2))) γ) ≡ fst (numeralL 2))
  (tagEq3 : fst (lookup (suc (suc (suc N3))) γ) ≡ fst (numeralL 3))
  (tagEq4 : fst (lookup (suc (suc (suc N4))) γ) ≡ fst (numeralL 4))
  (tagEq5 : fst (lookup (suc (suc (suc N5))) γ) ≡ fst (numeralL 5))
  (tagEq6 : fst (lookup (suc (suc (suc N6))) γ) ≡ fst (numeralL 6))
  (tagEq7 : fst (lookup (suc (suc (suc N7))) γ) ≡ fst (numeralL 7))
  (tagEq8 : fst (lookup (suc (suc (suc N8))) γ) ≡ fst (numeralL 8))
  (tagEq9 : fst (lookup (suc (suc (suc N9))) γ) ≡ fst (numeralL 9))
  (tagEq10 : fst (lookup (suc (suc (suc N10))) γ) ≡ fst (numeralL 10))
  (tagEq11 : fst (lookup (suc (suc (suc N11))) γ) ≡ fst (numeralL 11))
  (numK0 : ⟨ fst (numeralL 0) ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (numK1 : ⟨ fst (numeralL 1) ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (numK2 : ⟨ fst (numeralL 2) ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (numK3 : ⟨ fst (numeralL 3) ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (numK4 : ⟨ fst (numeralL 4) ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (numK5 : ⟨ fst (numeralL 5) ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (numK6 : ⟨ fst (numeralL 6) ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (numK7 : ⟨ fst (numeralL 7) ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (numK8 : ⟨ fst (numeralL 8) ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (numK9 : ⟨ fst (numeralL 9) ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (numK10 : ⟨ fst (numeralL 10) ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (numK11 : ⟨ fst (numeralL 11) ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (innerK : (k : ℕ) (a : S) → ⟨ fst (prʟ (numeralL k) a) ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (innerPairK : (k : ℕ) (a b : S) → ⟨ fst (prʟ (numeralL k) (prʟ a b)) ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (pairK : (a b : S) → ⟨ fst (prʟ a b) ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (carrierK : (v : S) → ⟨ fst v ∈ fst (lookup (suc (suc (suc w))) γ) ⟩
             → ⟨ fst v ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (arityK : (N v : S) → ⟨ fst v ∈ fst N ⟩
           → ⟨ fst v ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (witK : (w' : S) → ⟨ (w' ∷ γ) ⊨ ((var (suc (suc zero)) ∈̇ var zero)
               ∧̇ (closedAt zero ∧̇ shapedAt zero (suc (suc (suc (suc w)))))) ⟩
         → ⟨ fst w' ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (wCodesK : (w' : S) → (k : ℕ) → (c ar a b : S) → ⟨ fst c ∈ fst w' ⟩
            → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
            → ⟨ fst ar ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
              × ⟨ fst a ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
              × ⟨ fst b ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (wUnCodesK : (w' : S) → (k : ℕ) → (c ar a : S) → ⟨ fst c ∈ fst w' ⟩
              → fst c ≡ pr (fst ar) (pr (# k) (fst a))
              → ⟨ fst ar ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
                × ⟨ fst a ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (wEntryK : (w' x' y : S) → ⟨ pr (fst x') (fst y) ∈ fst w' ⟩
            → ⟨ fst x' ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
              × ⟨ fst y ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  -- the graph frame facts (the satGraph code set sits at slot 2 of
  -- the 3-deep graph environment)
  (twelve-out : (d e f : S) → ⟨ (f ∷ e ∷ d ∷ γ) ⊨ twelveAt (suc (suc zero)) (suc zero) zero ⟩
              → ⟨ (f ∷ e ∷ d ∷ γ) ⊨ SatGraphB.twelveB {n} w K N0 N1 N2 N3 N4 N5
                                           N6 N7 N8 N9 N10 N11 t0 t1 ⟩)
  (twelve-back : (d e f : S) → ⟨ (f ∷ e ∷ d ∷ γ) ⊨ SatGraphB.twelveB {n} w K N0 N1 N2 N3 N4 N5
                                            N6 N7 N8 N9 N10 N11 t0 t1 ⟩
               → ⟨ (f ∷ e ∷ d ∷ γ) ⊨ twelveAt (suc (suc zero)) (suc zero) zero ⟩)
  (gCodesK : (d e f : S) → (k : ℕ) → (c ar a b : S)
            → ⟨ fst c ∈ fst (lookup (suc (suc zero)) (f ∷ e ∷ d ∷ γ)) ⟩
            → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
            → ⟨ fst ar ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
              × ⟨ fst a ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
              × ⟨ fst b ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (gUnCodesK : (d e f : S) → (k : ℕ) → (c ar a : S)
              → ⟨ fst c ∈ fst (lookup (suc (suc zero)) (f ∷ e ∷ d ∷ γ)) ⟩
              → fst c ≡ pr (fst ar) (pr (# k) (fst a))
              → ⟨ fst ar ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
                × ⟨ fst a ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (gEntryK : (d e f : S) → (x' y : S) → ⟨ pr (fst x') (fst y) ∈ fst (lookup (suc (suc zero)) (f ∷ e ∷ d ∷ γ)) ⟩
            → ⟨ fst x' ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
              × ⟨ fst y ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (domEntryK : (d e f : S) → (x' y : S) → ⟨ pr (fst x') (fst y) ∈ fst (lookup (suc zero) (f ∷ e ∷ d ∷ γ)) ⟩
              → ⟨ fst x' ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
                × ⟨ fst y ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (domK : (d e f : S) → (x : S) → ⟨ fst x ∈ fst (lookup (suc (suc zero)) (f ∷ e ∷ d ∷ γ)) ⟩
         → ⟨ fst x ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
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
  -- the Defines leaf facts
  (keyValK : (t : S) → ⟨ (t ∷ γ) ⊨ tagAtL (suc (suc zero)) 1 zero ⟩
            → ⟨ fst t ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (envK : (E z : S) → ⟨ (E ∷ z ∷ γ) ⊨ envOneAt zero (suc zero) ⟩
         → ⟨ fst E ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (defPairK : (E z w' : S) → ⟨ (w' ∷ E ∷ z ∷ γ) ⊨ tagAtL zero 0 (suc (suc zero)) ⟩
             → ⟨ fst w' ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (satK : (z : S) → ⟨ (z ∷ γ) ⊨ ((var zero ∈̇ var (suc (suc (suc (suc w)))))
             ∧̇ ∃̇ (envOneAt zero (suc zero) ∧̇ (var zero ∈̇ var (suc (suc zero))))) ⟩
         → ⟨ fst z ∈ fst (lookup (suc (suc (suc K))) γ) ⟩) where

  module WA = WitnessAgree {8 + n} (suc (suc (suc w))) (suc zero) (suc (suc (suc K)))
                (suc (suc (suc N0))) (suc (suc (suc N1)))
                (suc (suc (suc N2))) (suc (suc (suc N3)))
                (suc (suc (suc N4))) (suc (suc (suc N5)))
                (suc (suc (suc N6))) (suc (suc (suc N7)))
                (suc (suc (suc N8))) (suc (suc (suc N9)))
                (suc (suc (suc N10))) (suc (suc (suc N11))) γ
                tagEq0 tagEq1 tagEq2 tagEq3 tagEq4 tagEq5 tagEq6 tagEq7
                tagEq8 tagEq9 tagEq10 tagEq11
                numK0 numK1 numK2 numK3 numK4 numK5 numK6 numK7
                numK8 numK9 numK10 numK11
                innerK innerPairK pairK carrierK arityK witK wCodesK wUnCodesK wEntryK

  module KA = P154.KeyAgree {8 + n} (suc zero) (suc (suc (suc N1))) (suc (suc (suc K))) γ 1
                tagEq1 numK1 keyValK

  module SG = P156.SatGraphAgree {n} w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 γ
                twelve-out twelve-back
                tagEq2 tagEq3 tagEq4 tagEq5 tagEq8 tagEq9 tagEq10 tagEq11
                numK2 numK3 numK4 numK5 numK8 numK9 numK10 numK11
                innerK innerPairK pairK gCodesK gUnCodesK gEntryK domEntryK domK graphWitK

  module DA = P154.DefinesAgree {8 + n} (suc (suc zero)) (suc (suc (suc w))) zero
                (suc (suc (suc K))) (suc (suc (suc N0))) γ
                tagEq0 numK0 envK defPairK satK

  ic-out : ⟨ γ ⊨ isCodeAt (suc zero) (suc (suc (suc w))) ⟩
         → ⟨ γ ⊨ isCodeBS (suc zero) (suc (suc (suc w))) (suc (suc (suc K)))
               (suc (suc (suc N0))) (suc (suc (suc N1)))
               (suc (suc (suc N2))) (suc (suc (suc N3)))
               (suc (suc (suc N4))) (suc (suc (suc N5)))
               (suc (suc (suc N6))) (suc (suc (suc N7)))
               (suc (suc (suc N8))) (suc (suc (suc N9)))
               (suc (suc (suc N10))) (suc (suc (suc N11))) ⟩
  ic-out (hk , hw) = (KA.out hk , WA.out hw)

  ic-back : ⟨ γ ⊨ isCodeBS (suc zero) (suc (suc (suc w))) (suc (suc (suc K)))
               (suc (suc (suc N0))) (suc (suc (suc N1)))
               (suc (suc (suc N2))) (suc (suc (suc N3)))
               (suc (suc (suc N4))) (suc (suc (suc N5)))
               (suc (suc (suc N6))) (suc (suc (suc N7)))
               (suc (suc (suc N8))) (suc (suc (suc N9)))
               (suc (suc (suc N10))) (suc (suc (suc N11))) ⟩
         → ⟨ γ ⊨ isCodeAt (suc zero) (suc (suc (suc w))) ⟩
  ic-back (hk , hw) = (KA.back hk , WA.back hw)

  out : ⟨ γ ⊨ DefBody {5 + n} w ⟩ → ⟨ γ ⊨ DefBodyB w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 ⟩
  out (hcode , (hgraph , hdef)) =
    ( ic-out hcode
    , ( SG.out hgraph
      , DA.out hdef ) )

  back : ⟨ γ ⊨ DefBodyB w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 ⟩
       → ⟨ γ ⊨ DefBody {5 + n} w ⟩
  back (hcode , (hgraph , hdef)) =
    ( ic-back hcode
    , ( SG.back hgraph
      , DA.back hdef ) )

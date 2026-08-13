# The upper agreement

<!--en-->
The upper agreement is the conjunction of the last six row agreements:
top, bottom, existential, universal, all-in and exists-in. It states the
forty-three site facts those rows use at an abstract environment and proves
both directions against the twelve-row target.
<!--zh-->
上位一致是后六行一致式的合取：顶、底、存在、全称、全含与存在含。它把这六行用到的四十三个场地事实陈述于一个抽象环境，并对十二行目标证明两个方向。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Condensation.UpperAgree {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _∈̇_; _∧̇_ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Axioms.Numerals {ℓ} using ( numeralL; sucʟ; sucʟ-fst )
open import L.Coding.Model {ℓ}
  using ( prʟ; prʟ-fst; envSetAt; envOverAt; tmValAt; consAtL; subValSuccAt
        ; topClauseAt; botClauseAt; existClauseAt; forallClauseAt
        ; allInClauseAt; exInClauseAt )
open import L.Coding.Graph {ℓ} lem using ( twelveAt )
open import L.Condensation {ℓ} lem using
  ( succU; keyU; module Top; module Bot; module Exist; module Forall
  ; module AllIn; module ExIn; module TopAgree; module BotAgree
  ; module ExistAgree; module ForallAgree; module AllInAgree
  ; module ExInAgree )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet using ( #_; sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- THE TIED SUCCESSOR-KEY FACTS, derived once from sucK and pairK
-- ([LJ-1.109] TiesSupplied).  sucK is the successor closure, a
-- telescope fact of the frame, never a KFacts record field (P-x).
-- key-un-tied transports the L-pair of the L-successor along
-- sucʟ-fst and prʟ-fst.  Generic in the K slot and gamma, so
-- UpperAgree and TwelveAgree instantiate the same derivation (DD4).
module SuccKeyTies {m : ℕ} (K : Fin m) (γ : S ^ m)
  (sucK : (a : S) → ⟨ fst a ∈ fst (lookup K γ) ⟩
          → ⟨ sucV (fst a) ∈ fst (lookup K γ) ⟩)
  (pairK : (a b : S) → ⟨ fst a ∈ fst (lookup K γ) ⟩
           → ⟨ fst b ∈ fst (lookup K γ) ⟩
           → ⟨ fst (prʟ a b) ∈ fst (lookup K γ) ⟩) where

  succ-tied : (ar : S) → ⟨ fst ar ∈ fst (lookup K γ) ⟩
            → ⟨ sucV (fst ar) ∈ fst (lookup K γ) ⟩
  succ-tied ar arK = sucK ar arK

  key-un-tied : (ar a : S) → ⟨ fst ar ∈ fst (lookup K γ) ⟩
              → ⟨ fst a ∈ fst (lookup K γ) ⟩
              → ⟨ pr (sucV (fst ar)) (fst a) ∈ fst (lookup K γ) ⟩
  key-un-tied ar a arK aK =
    subst (λ w → ⟨ w ∈ fst (lookup K γ) ⟩)
      (prʟ-fst (sucʟ ar) a ∙ cong₂ pr (sucʟ-fst ar) refl)
      (pairK (sucʟ ar) a
        (transport (sym (cong (λ w → ⟨ w ∈ fst (lookup K γ) ⟩) (sucʟ-fst ar)))
          (sucK ar arK))
        aK)

module UpperAgree {n : ℕ}
  (N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K : Fin (5 + n))
  (γ : S ^ (11 + n))
  (tagEq6 : fst (lookup (suc (suc (suc (suc (suc (suc N6)))))) γ) ≡ fst (numeralL 6))
  (tagEq7 : fst (lookup (suc (suc (suc (suc (suc (suc N7)))))) γ) ≡ fst (numeralL 7))
  (tagEq8 : fst (lookup (suc (suc (suc (suc (suc (suc N8)))))) γ) ≡ fst (numeralL 8))
  (tagEq9 : fst (lookup (suc (suc (suc (suc (suc (suc N9)))))) γ) ≡ fst (numeralL 9))
  (tagEq10 : fst (lookup (suc (suc (suc (suc (suc (suc N10)))))) γ) ≡ fst (numeralL 10))
  (tagEq11 : fst (lookup (suc (suc (suc (suc (suc (suc N11)))))) γ) ≡ fst (numeralL 11))
  (numK6 : ⟨ fst (numeralL 6) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (numK7 : ⟨ fst (numeralL 7) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (numK8 : ⟨ fst (numeralL 8) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (numK9 : ⟨ fst (numeralL 9) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (numK10 : ⟨ fst (numeralL 10) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (numK11 : ⟨ fst (numeralL 11) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (innerK : (k : ℕ) (p : S) → ⟨ fst p ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
             → ⟨ fst (prʟ (numeralL k) p) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (pairK : (a b : S) → ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
             → ⟨ fst b ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
             → ⟨ fst (prʟ a b) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (arityK : (N v : S) → ⟨ fst v ∈ fst N ⟩
             → ⟨ fst N ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
             → ⟨ fst v ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
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
          → ⟨ pr (fst c) (fst yc) ∈ fst (lookup (suc zero) γ) ⟩
          → ⟨ fst yc ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (valK-un : (k : ℕ) (c ar a yc : S) → ⟨ fst c ∈ fst (lookup (suc (suc zero)) γ) ⟩
             → fst c ≡ pr (fst ar) (pr (# k) (fst a))
             → ⟨ pr (fst c) (fst yc) ∈ fst (lookup (suc zero) γ) ⟩
             → ⟨ fst yc ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (t0eq : fst (lookup (suc (suc (suc (suc (suc (suc t0)))))) γ) ≡ fst (numeralL 0))
  (t1eq : fst (lookup (suc (suc (suc (suc (suc (suc t1)))))) γ) ≡ fst (numeralL 1))
  (t0K : ⟨ fst (lookup (suc (suc (suc (suc (suc (suc t0)))))) γ)
           ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (num1K : ⟨ fst (numeralL 1) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (envK-neg : (ya yc a ar c E : S) → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨
                envSetAt zero (suc (suc (suc (suc zero))))
                          (suc (suc (suc (suc (suc (suc zero)))))) ⟩
             → ⟨ fst E ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (envK-top : (yc a ar c E : S) → ⟨ (E ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨
                envSetAt zero (suc (suc (suc zero)))
                          (suc (suc (suc (suc (suc zero))))) ⟩
             → ⟨ fst E ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (envK-allin : (E ya yc b a ar c : S) → ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
                  envSetAt zero (suc (suc (suc (suc (suc zero)))))
                            (suc (suc (suc (suc (suc (suc (suc zero))))))) ⟩
               → ⟨ fst E ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (envInK-neg : (ya yc a ar c E z : S) → ⟨ (z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨
                  envOverAt zero (suc (suc (suc (suc (suc zero)))))
                              (suc (suc (suc (suc (suc (suc (suc zero))))))) ⟩
               → ⟨ fst z ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (envInK-top : (yc a ar c E z : S) → ⟨ (z ∷ E ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨
                  envOverAt zero (suc (suc (suc (suc zero))))
                              (suc (suc (suc (suc (suc (suc zero)))))) ⟩
               → ⟨ fst z ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (envInK-imp : (E ya yc b a ar c z : S) → ⟨ (z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
                  envOverAt zero (suc (suc (suc (suc (suc (suc zero))))))
                              (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) ⟩
               → ⟨ fst z ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (wKfact : (E ya yc b a ar c z w : S) → ⟨ (w ∷ z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
              tmValAt (suc (suc (suc (suc (suc (suc zero))))))
                      (suc zero)
                      zero ⟩
            → ⟨ fst w ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc K))))))))))))))
                              (z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)) ⟩)
  (sucK : (a : S) → ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
          → ⟨ sucV (fst a) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (subK-un : (ya yc a ar c E : S) → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨
               subValSuccAt (suc (suc (suc (suc (suc (suc (suc zero)))))))
                            (suc (suc (suc (suc zero))))
                            (suc (suc (suc zero)))
                            (suc zero) ⟩
             → ⟨ fst ya ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (consK-exist : (ya yc a ar c E z x e' : S) → ⟨ (e' ∷ x ∷ z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨
                   consAtL zero (suc zero) (suc (suc zero))
                   ∧̇ (var zero ∈̇ var (suc (suc (suc (suc zero))))) ⟩
                 → ⟨ fst e' ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc K))))))))))))))
                                   (x ∷ z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ)) ⟩)
  (consK-forall : (ya yc a ar c E z x e' : S) → ⟨ (e' ∷ x ∷ z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨
                    consAtL zero (suc zero) (suc (suc zero)) ⟩
                  → ⟨ fst e' ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc K))))))))))))))
                                    (x ∷ z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ)) ⟩)
  (subK-allin : (E ya yc b a ar c : S) → ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
                  subValSuccAt (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
                               (suc (suc (suc (suc (suc zero)))))
                               (suc (suc (suc zero)))
                               (suc zero) ⟩
                → ⟨ fst ya ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (consK-allin : (E ya yc b a ar c z w x e' : S) → ⟨ (e' ∷ x ∷ w ∷ z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
                   consAtL zero (suc zero) (suc (suc (suc zero))) ⟩
                 → ⟨ fst e' ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc K))))))))))))))))
                                   (x ∷ w ∷ z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)) ⟩)
  where

  -- The four tied key facts of the upper rows, derived once from sucK
  -- and pairK ([LJ-1.109] TiesSupplied).  The site memberships (arK,
  -- aK, bK) are the rows' binders; the facts are derivations, not
  -- hypotheses (C-38).
  module KT = SuccKeyTies {11 + n} (suc (suc (suc (suc (suc (suc K)))))) γ sucK pairK

  succK-tied : (N : Fin (11 + n)) (E ya yc a ar c : S)
             → ⟨ fst ar ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
             → succU {11 + n} (suc (suc zero)) (suc zero) zero N
                      (suc (suc (suc (suc (suc (suc K)))))) γ E ya yc a ar c
  succK-tied N E ya yc a ar c arK = KT.succ-tied ar arK

  keyK-un-tied : (N : Fin (11 + n)) (E ya yc a ar c : S)
               → ⟨ fst ar ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
               → ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
               → keyU {11 + n} (suc (suc zero)) (suc zero) zero N
                        (suc (suc (suc (suc (suc (suc K)))))) γ E ya yc a ar c
  keyK-un-tied N E ya yc a ar c arK aK = KT.key-un-tied ar a arK aK

  succK-allin-tied : (E ya yc b a ar c : S)
                   → ⟨ fst ar ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
                   → ⟨ sucV (fst ar)
                        ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
  succK-allin-tied E ya yc b a ar c arK = KT.succ-tied ar arK

  keyK-allin-tied : (E ya yc b a ar c : S)
                  → ⟨ fst ar ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
                  → ⟨ fst b ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
                  → ⟨ pr (sucV (fst ar)) (fst b)
                       ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
  keyK-allin-tied E ya yc b a ar c arK bK = KT.key-un-tied ar b arK bK

  module T = TopAgree {11 + n} (suc (suc zero)) (suc zero) zero
               (suc (suc (suc (suc (suc (suc N6)))))) (suc (suc (suc (suc (suc (suc K)))))) γ
               tagEq6 numK6
               (λ a aK → innerK 6 a aK) arityK (codesK-un 6) (valK-un 6)
               envK-top envInK-top

  module B = BotAgree {11 + n} (suc (suc zero)) (suc zero) zero
               (suc (suc (suc (suc (suc (suc N7)))))) (suc (suc (suc (suc (suc (suc K)))))) γ
               tagEq7 numK7
               (λ a aK → innerK 7 a aK) (codesK-un 7) (valK-un 7)

  module X = ExistAgree {11 + n} (suc (suc zero)) (suc zero) zero
               (suc (suc (suc (suc (suc (suc N8)))))) (suc (suc (suc (suc (suc (suc K)))))) γ
               tagEq8 numK8
               (λ a aK → innerK 8 a aK) arityK (codesK-un 8) (valK-un 8)
               (succK-tied (suc (suc (suc (suc (suc (suc N8)))))))
               (keyK-un-tied (suc (suc (suc (suc (suc (suc N8))))))) subK-un
               envK-neg envInK-neg consK-exist

  module F = ForallAgree {11 + n} (suc (suc zero)) (suc zero) zero
               (suc (suc (suc (suc (suc (suc N9)))))) (suc (suc (suc (suc (suc (suc K)))))) γ
               tagEq9 numK9
               (λ a aK → innerK 9 a aK) arityK (codesK-un 9) (valK-un 9)
               (succK-tied (suc (suc (suc (suc (suc (suc N9)))))))
               (keyK-un-tied (suc (suc (suc (suc (suc (suc N9))))))) subK-un
               envK-neg envInK-neg consK-forall

  module AI = AllInAgree {11 + n} (suc (suc zero)) (suc zero) zero
                (suc (suc (suc (suc (suc (suc N10)))))) (suc (suc (suc (suc (suc (suc K)))))) (suc (suc (suc (suc (suc (suc t0)))))) (suc (suc (suc (suc (suc (suc t1)))))) γ
                tagEq10 numK10
                (λ a b aK bK → innerK 10 (prʟ a b) (pairK a b aK bK)) (λ a b aK bK → pairK a b aK bK) arityK (codesK 10) (valK 10)
                succK-allin-tied keyK-allin-tied subK-allin envK-allin envInK-imp
                t0eq t1eq t0K num1K wKfact consK-allin

  module EI = ExInAgree {11 + n} (suc (suc zero)) (suc zero) zero
                (suc (suc (suc (suc (suc (suc N11)))))) (suc (suc (suc (suc (suc (suc K)))))) (suc (suc (suc (suc (suc (suc t0)))))) (suc (suc (suc (suc (suc (suc t1)))))) γ
                tagEq11 numK11
                (λ a b aK bK → innerK 11 (prʟ a b) (pairK a b aK bK)) (λ a b aK bK → pairK a b aK bK) arityK (codesK 11) (valK 11)
                succK-allin-tied keyK-allin-tied subK-allin envK-allin envInK-imp
                t0eq t1eq t0K num1K wKfact consK-allin

  sixB : Formula S (11 + n)
  sixB =
    Top.topBndAt {11 + n} (suc (suc zero)) (suc zero) zero
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
    ∧̇ (ExIn.exInBndAt {11 + n} (suc (suc zero)) (suc zero) zero
      (suc (suc (suc (suc (suc (suc N11))))))
      (suc (suc (suc (suc (suc (suc K))))))
      (suc (suc (suc (suc (suc (suc t0))))))
      (suc (suc (suc (suc (suc (suc t1))))))
    )))))

  sixAt : Formula S (11 + n)
  sixAt =
    topClauseAt {11 + n} (suc (suc zero)) (suc zero) zero
    ∧̇ (botClauseAt {11 + n} (suc (suc zero)) (suc zero)
    ∧̇ (existClauseAt {11 + n} (suc (suc zero)) (suc zero) zero
    ∧̇ (forallClauseAt {11 + n} (suc (suc zero)) (suc zero) zero
    ∧̇ (allInClauseAt {11 + n} (suc (suc zero)) (suc zero) zero
    ∧̇ (exInClauseAt {11 + n} (suc (suc zero)) (suc zero) zero
    )))))

  out : ⟨ γ ⊨ twelveAt (suc (suc zero)) (suc zero) zero ⟩ → ⟨ γ ⊨ sixB ⟩
  out h =
    ( T.out (h .snd .snd .snd .snd .snd .snd .fst)
    , ( B.bot-out (h .snd .snd .snd .snd .snd .snd .snd .fst)
      , ( X.out (h .snd .snd .snd .snd .snd .snd .snd .snd .fst)
        , ( F.out (h .snd .snd .snd .snd .snd .snd .snd .snd .snd .fst)
          , ( AI.out (h .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .fst)
            , EI.out (h .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd) )))))

  back : ⟨ γ ⊨ sixB ⟩ → ⟨ γ ⊨ sixAt ⟩
  back h =
    ( T.back (h .fst)
    , ( B.bot-in (h .snd .fst)
      , ( X.back (h .snd .snd .fst)
        , ( F.back (h .snd .snd .snd .fst)
          , ( AI.back (h .snd .snd .snd .snd .fst)
            , EI.back (h .snd .snd .snd .snd .snd) )))))
```

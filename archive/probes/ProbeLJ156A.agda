{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.56] probe A: the closedness transfer, the domain transfer and
-- the shapedness atoms at the generic frame.  Built on the cured
-- master (arTagBS, isTmBS, satGraphB).  Every negative is measured:
-- the pre-cure arTagBS reading is shown broken by the frame transfer
-- that now closes, and the pre-cure isTmBS gap by the disjointness of
-- the constant and variable branches (constVarDisjoint).
--
-- Untracked probe; never committed.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ156A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

import FOL.Absoluteness
open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _∧̇_; _∨̇_; _⇒̇_; _≐_; _∈̇_; ∃̇_; ∃̇∈; ∀̇∈ )
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
open import L.Coding.Shape {ℓ} using ( isTmAt )
open import L.Coding.Graph {ℓ} lem using ( satGraphAt; twelveAt )
open import L.Condensation {ℓ} lem using
  ( arTagBS; arTagPairBS; binShapeBS; unShapeBS; bothSameB; oneSameB
  ; oneSuccB; succSndB; closedBS; domB; tagBS; isTmBS; bothTmBS; fstTmBS
  ; module SatGraphB )
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

private
  PairIs : V ℓ → V ℓ → Ω
  PairIs a p = (a ≡ p) , setIsSet a p

-- =====================================================================
-- SECTION 1. THE CLOSEDNESS FRAME SHAPES.
-- arTagBS at the 3-deep frame and arTagPairBS at the 4-deep frame,
-- against the machine's arityTagAtL/arityTagPairAtL at the same
-- frames.  The unary shape is the cured master arTagBS; its transfer
-- closes (the probe's consumer test for the cure).
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

  in' : ⟨ γ ⊨ arityTagAtL (suc (suc zero)) (suc zero) k zero ⟩
      → ⟨ γ ⊨ arTagBS tag K ⟩
  in' h = PT.rec squash₁
    (λ { (z , (p , tz)) →
      let p' : fst (lookup (suc (suc (suc zero))) (z ∷ γ))
              ≡ pr (fst (lookup (suc (suc zero)) (z ∷ γ)))
                   (fst (lookup zero (z ∷ γ)))
          p' = transport (cong fst (prAtL-adequate (suc (suc (suc zero)))
                (suc (suc zero)) zero (z ∷ γ))) p
          tz' : fst (lookup zero (z ∷ γ))
               ≡ pr (# k) (fst (lookup (suc zero) (z ∷ γ)))
          tz' = transport (cong fst (tagAtL-adequate zero k (suc zero) (z ∷ γ))) tz
          a₀ : S
          a₀ = lookup zero γ
          zK : ⟨ fst z ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
          zK = subst (λ w → ⟨ w ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
                 (sym tz')
                 (subst (λ w → ⟨ w ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
                   (prʟ-fst (numeralL k) a₀ ∙ cong₂ pr (numeralL-fst k) refl)
                   (innerK a₀))
          zt : ⟨ (numeralL k ∷ z ∷ γ) ⊨ prAtL (suc zero) zero (suc (suc zero)) ⟩
          zt = transport (cong fst (sym (prAtL-adequate (suc zero) zero
                 (suc (suc zero)) (numeralL k ∷ z ∷ γ))))
               (tz' ∙ cong₂ pr (sym (numeralL-fst k)) refl)
      in ∣ z , ( zK
               , ( p
                 , ∣ numeralL k
                   , ( numK
                     , ( sym tagEq
                       , zt ) )
                   ∣₁ ) ) ∣₁ })
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

  in' : ⟨ γ ⊨ arityTagPairAtL (suc (suc (suc zero))) (suc (suc zero)) k (suc zero) zero ⟩
      → ⟨ γ ⊨ arTagPairBS tag K ⟩
  in' h = PT.rec squash₁
    (λ { (z , (p , tz)) →
      let p' : fst (lookup (suc (suc (suc (suc zero)))) (z ∷ γ))
              ≡ pr (fst (lookup (suc (suc (suc zero))) (z ∷ γ)))
                   (fst (lookup zero (z ∷ γ)))
          p' = transport (cong fst (prAtL-adequate (suc (suc (suc (suc zero))))
                (suc (suc (suc zero))) zero (z ∷ γ))) p
          tz' : fst (lookup zero (z ∷ γ))
               ≡ pr (# k) (pr (fst (lookup (suc (suc zero)) (z ∷ γ)))
                              (fst (lookup (suc zero) (z ∷ γ))))
          tz' = transport (cong fst (tagPairAtL-adequate zero k (suc (suc zero))
                (suc zero) (z ∷ γ))) tz
          a₀ : S
          a₀ = lookup (suc zero) γ
          b₀ : S
          b₀ = lookup zero γ
          zK : ⟨ fst z ∈ fst (lookup (suc (suc (suc (suc K)))) γ) ⟩
          zK = subst (λ w → ⟨ w ∈ fst (lookup (suc (suc (suc (suc K)))) γ) ⟩)
                 (sym tz')
                 (subst (λ w → ⟨ w ∈ fst (lookup (suc (suc (suc (suc K)))) γ) ⟩)
                   (prʟ-fst (numeralL k) (prʟ a₀ b₀)
                    ∙ cong₂ pr (numeralL-fst k) (prʟ-fst a₀ b₀))
                   (innerK a₀ b₀))
          zt : ⟨ (prʟ a₀ b₀ ∷ numeralL k ∷ z ∷ γ)
                  ⊨ prAtL (suc (suc zero)) (suc zero) zero ⟩
          zt = transport (cong fst (sym (prAtL-adequate (suc (suc zero)) (suc zero) zero
                 (prʟ a₀ b₀ ∷ numeralL k ∷ z ∷ γ))))
               (tz' ∙ cong₂ pr (sym (numeralL-fst k)) (sym (prʟ-fst a₀ b₀)))
          wb : ⟨ (prʟ a₀ b₀ ∷ numeralL k ∷ z ∷ γ)
                  ⊨ prAtL zero (suc (suc (suc (suc zero))))
                            (suc (suc (suc zero))) ⟩
          wb = transport (cong fst (sym (prAtL-adequate zero (suc (suc (suc (suc zero))))
                 (suc (suc (suc zero)))
                 (prʟ a₀ b₀ ∷ numeralL k ∷ z ∷ γ))))
               (prʟ-fst a₀ b₀)
      in ∣ z , ( zK
               , ( p
                 , ∣ numeralL k
                   , ( numK
                     , ∣ prʟ a₀ b₀
                       , ( pairK a₀ b₀
                         , ( sym tagEq , ( zt , wb ) ) )
                       ∣₁ )
                   ∣₁ ) ) ∣₁ })
    h

-- =====================================================================
-- SECTION 2. THE GENERIC FRAME AGREEMENTS.
-- binShapeBS/unShapeBS against binShapeAt/unShapeAt at the same
-- frame, under the site facts and a pointwise rel transfer.  The rel
-- transfer is a parameter; the closedness relations instantiate it.
-- =====================================================================
module BinFrameAgree {n : ℕ} (C tag K : Fin n) (k : ℕ) (γ : S ^ n)
  (tagEq : fst (lookup tag γ) ≡ fst (numeralL k))
  (numK : ⟨ fst (numeralL k) ∈ fst (lookup K γ) ⟩)
  (innerK : (a b : S) → ⟨ fst (prʟ (numeralL k) (prʟ a b)) ∈ fst (lookup K γ) ⟩)
  (pairK : (a b : S) → ⟨ fst (prʟ a b) ∈ fst (lookup K γ) ⟩)
  (codesK : (c ar a b : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
           → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
           → ⟨ fst ar ∈ fst (lookup K γ) ⟩
             × ⟨ fst a ∈ fst (lookup K γ) ⟩ × ⟨ fst b ∈ fst (lookup K γ) ⟩)
  (relB relM : Formula S (4 + n))
  (relOut : (b a ar c : S) → ⟨ (b ∷ a ∷ ar ∷ c ∷ γ) ⊨ relB ⟩
           → ⟨ (b ∷ a ∷ ar ∷ c ∷ γ) ⊨ relM ⟩)
  (relBack : (b a ar c : S) → ⟨ (b ∷ a ∷ ar ∷ c ∷ γ) ⊨ relM ⟩
           → ⟨ (b ∷ a ∷ ar ∷ c ∷ γ) ⊨ relB ⟩) where

  out : ⟨ γ ⊨ binShapeAt C k relM ⟩ → ⟨ γ ⊨ binShapeBS C tag K relB ⟩
  out h = λ c c∈ ar arK a aK b bK shapeB →
    let module S = BinShapeClosed {n} tag K k (b ∷ a ∷ ar ∷ c ∷ γ)
                     tagEq numK innerK pairK
    in relBack b a ar c
         (binShape-out C k relM γ h c ar a b c∈
           (subst fst (arityTagPairAtL-adequate
              (suc (suc (suc zero))) (suc (suc zero)) k (suc zero) zero
              (b ∷ a ∷ ar ∷ c ∷ γ)) (S.out shapeB)))

  back : ⟨ γ ⊨ binShapeBS C tag K relB ⟩ → ⟨ γ ⊨ binShapeAt C k relM ⟩
  back h = binShape-in C k relM γ go
    where
    go : (c ar a b : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
       → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
       → ⟨ (b ∷ a ∷ ar ∷ c ∷ γ) ⊨ relM ⟩
    go c ar a b c∈ shapeM =
      relOut b a ar c (h c c∈ ar arK a aK b bK
        (S.in' (subst ⟨_⟩ (sym (arityTagPairAtL-adequate
           (suc (suc (suc zero))) (suc (suc zero)) k (suc zero) zero
           (b ∷ a ∷ ar ∷ c ∷ γ))) shapeM)))
      where
      module S = BinShapeClosed {n} tag K k (b ∷ a ∷ ar ∷ c ∷ γ)
                   tagEq numK innerK pairK
      ks : ⟨ fst ar ∈ fst (lookup K γ) ⟩
         × ⟨ fst a ∈ fst (lookup K γ) ⟩ × ⟨ fst b ∈ fst (lookup K γ) ⟩
      ks = codesK c ar a b c∈ shapeM
      arK = ks .fst
      aK = ks .snd .fst
      bK = ks .snd .snd

module UnFrameAgree {n : ℕ} (C tag K : Fin n) (k : ℕ) (γ : S ^ n)
  (tagEq : fst (lookup tag γ) ≡ fst (numeralL k))
  (numK : ⟨ fst (numeralL k) ∈ fst (lookup K γ) ⟩)
  (innerK : (a : S) → ⟨ fst (prʟ (numeralL k) a) ∈ fst (lookup K γ) ⟩)
  (unCodesK : (c ar a : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
             → fst c ≡ pr (fst ar) (pr (# k) (fst a))
             → ⟨ fst ar ∈ fst (lookup K γ) ⟩ × ⟨ fst a ∈ fst (lookup K γ) ⟩)
  (relB relM : Formula S (3 + n))
  (relOut : (a ar c : S) → ⟨ (a ∷ ar ∷ c ∷ γ) ⊨ relB ⟩
           → ⟨ (a ∷ ar ∷ c ∷ γ) ⊨ relM ⟩)
  (relBack : (a ar c : S) → ⟨ (a ∷ ar ∷ c ∷ γ) ⊨ relM ⟩
           → ⟨ (a ∷ ar ∷ c ∷ γ) ⊨ relB ⟩) where

  out : ⟨ γ ⊨ unShapeAt C k relM ⟩ → ⟨ γ ⊨ unShapeBS C tag K relB ⟩
  out h = λ c c∈ ar arK a aK shapeB →
    let module S = UnShapeClosed {n} tag K k (a ∷ ar ∷ c ∷ γ)
                     tagEq numK innerK
    in relBack a ar c
         (unShape-out C k relM γ h c ar a c∈
           (subst fst (arityTagAtL-adequate
              (suc (suc zero)) (suc zero) k zero
              (a ∷ ar ∷ c ∷ γ)) (S.out shapeB)))

  back : ⟨ γ ⊨ unShapeBS C tag K relB ⟩ → ⟨ γ ⊨ unShapeAt C k relM ⟩
  back h = unShape-in C k relM γ go
    where
    go : (c ar a : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
       → fst c ≡ pr (fst ar) (pr (# k) (fst a))
       → ⟨ (a ∷ ar ∷ c ∷ γ) ⊨ relM ⟩
    go c ar a c∈ shapeM =
      relOut a ar c (h c c∈ ar arK a aK
        (S.in' (subst ⟨_⟩ (sym (arityTagAtL-adequate
           (suc (suc zero)) (suc zero) k zero
           (a ∷ ar ∷ c ∷ γ))) shapeM)))
      where
      module S = UnShapeClosed {n} tag K k (a ∷ ar ∷ c ∷ γ)
                   tagEq numK innerK
      ks : ⟨ fst ar ∈ fst (lookup K γ) ⟩ × ⟨ fst a ∈ fst (lookup K γ) ⟩
      ks = unCodesK c ar a c∈ shapeM
      arK = ks .fst
      aK = ks .snd

-- =====================================================================
-- SECTION 3. THE CLOSEDNESS RELATIONS, POINTWISE.
-- bothSameB/oneSameB agree with the machine definitionally (the
-- [LJ-1.55] cure); oneSuccB/succSndB differ only by the bounded
-- existential, whose witness lies in K by the entryK site fact.
-- =====================================================================
module BothSameRel {n : ℕ} (C : Fin n) (γ : S ^ n) where
  out : (b a ar c : S) → ⟨ (b ∷ a ∷ ar ∷ c ∷ γ) ⊨ bothSameB C ⟩
                       → ⟨ (b ∷ a ∷ ar ∷ c ∷ γ) ⊨ bothSameAt C ⟩
  out b a ar c h = h
  back : (b a ar c : S) → ⟨ (b ∷ a ∷ ar ∷ c ∷ γ) ⊨ bothSameAt C ⟩
                        → ⟨ (b ∷ a ∷ ar ∷ c ∷ γ) ⊨ bothSameB C ⟩
  back b a ar c h = h

module OneSameRel {n : ℕ} (C : Fin n) (γ : S ^ n) where
  out : (a ar c : S) → ⟨ (a ∷ ar ∷ c ∷ γ) ⊨ oneSameB C ⟩
                     → ⟨ (a ∷ ar ∷ c ∷ γ) ⊨ oneSameAt C ⟩
  out a ar c h = h
  back : (a ar c : S) → ⟨ (a ∷ ar ∷ c ∷ γ) ⊨ oneSameAt C ⟩
                      → ⟨ (a ∷ ar ∷ c ∷ γ) ⊨ oneSameB C ⟩
  back a ar c h = h

module OneSuccRel {n : ℕ} (C K : Fin n) (γ : S ^ n)
  (entryK : (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst (lookup C γ) ⟩
           → ⟨ fst x ∈ fst (lookup K γ) ⟩ × ⟨ fst y ∈ fst (lookup K γ) ⟩) where

  out : (a ar c : S) → ⟨ (a ∷ ar ∷ c ∷ γ) ⊨ oneSuccAt C ⟩
                     → ⟨ (a ∷ ar ∷ c ∷ γ) ⊨ oneSuccB C K ⟩
  out a ar c h = PT.rec squash₁ go h
    where
    go : Σ[ z ∈ S ]
         ⟨ (z ∷ a ∷ ar ∷ c ∷ γ) ⊨ (sucAtL (suc (suc zero)) zero
                                   ∧̇ appAt (suc (suc (suc (suc C)))) zero (suc zero)) ⟩
       → ⟨ (a ∷ ar ∷ c ∷ γ) ⊨ oneSuccB C K ⟩
    go (z , (sz , ap)) = ∣ z , ( zK , ( sz , ap ) ) ∣₁
      where
      zK : ⟨ fst z ∈ fst (lookup (suc (suc (suc K))) (a ∷ ar ∷ c ∷ γ)) ⟩
      zK = entryK z a
             (subst ⟨_⟩ (appAt-adequate (suc (suc (suc (suc C)))) zero (suc zero)
                (z ∷ a ∷ ar ∷ c ∷ γ)) ap) .fst

  back : (a ar c : S) → ⟨ (a ∷ ar ∷ c ∷ γ) ⊨ oneSuccB C K ⟩
                      → ⟨ (a ∷ ar ∷ c ∷ γ) ⊨ oneSuccAt C ⟩
  back a ar c = PT.map (λ { (z , _ , (sz , ap)) → z , (sz , ap) })

module SuccSndRel {n : ℕ} (C K : Fin n) (γ : S ^ n)
  (entryK : (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst (lookup C γ) ⟩
           → ⟨ fst x ∈ fst (lookup K γ) ⟩ × ⟨ fst y ∈ fst (lookup K γ) ⟩) where

  out : (b a ar c : S) → ⟨ (b ∷ a ∷ ar ∷ c ∷ γ) ⊨ succSndAt C ⟩
                       → ⟨ (b ∷ a ∷ ar ∷ c ∷ γ) ⊨ succSndB C K ⟩
  out b a ar c h = PT.rec squash₁ go h
    where
    go : Σ[ z ∈ S ]
         ⟨ (z ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ (sucAtL (suc (suc (suc zero))) zero
                                   ∧̇ appAt (suc (suc (suc (suc (suc C))))) zero (suc zero)) ⟩
       → ⟨ (b ∷ a ∷ ar ∷ c ∷ γ) ⊨ succSndB C K ⟩
    go (z , (sz , ap)) = ∣ z , ( zK , ( sz , ap ) ) ∣₁
      where
      zK : ⟨ fst z ∈ fst (lookup (suc (suc (suc (suc K)))) (b ∷ a ∷ ar ∷ c ∷ γ)) ⟩
      zK = entryK z b
             (subst ⟨_⟩ (appAt-adequate (suc (suc (suc (suc (suc C))))) zero (suc zero)
                (z ∷ b ∷ a ∷ ar ∷ c ∷ γ)) ap) .fst

  back : (b a ar c : S) → ⟨ (b ∷ a ∷ ar ∷ c ∷ γ) ⊨ succSndB C K ⟩
                        → ⟨ (b ∷ a ∷ ar ∷ c ∷ γ) ⊨ succSndAt C ⟩
  back b a ar c = PT.map (λ { (z , _ , (sz , ap)) → z , (sz , ap) })

-- =====================================================================
-- SECTION 4. THE EIGHT-FRAME CLOSEDNESS TRANSFER.
-- closedBS C K N2 N3 N4 N5 N8 N9 N10 N11 against closedAt C at the
-- same frame, both directions, under the site-fact bundle.  Each row
-- instantiates the generic frame agreement; the conjunction threads.
-- =====================================================================
module ClosedAgree {n : ℕ} (C K N2 N3 N4 N5 N8 N9 N10 N11 : Fin n)
  (γ : S ^ n)
  (tagEq2 : fst (lookup N2 γ) ≡ fst (numeralL 2))
  (tagEq3 : fst (lookup N3 γ) ≡ fst (numeralL 3))
  (tagEq4 : fst (lookup N4 γ) ≡ fst (numeralL 4))
  (tagEq5 : fst (lookup N5 γ) ≡ fst (numeralL 5))
  (tagEq8 : fst (lookup N8 γ) ≡ fst (numeralL 8))
  (tagEq9 : fst (lookup N9 γ) ≡ fst (numeralL 9))
  (tagEq10 : fst (lookup N10 γ) ≡ fst (numeralL 10))
  (tagEq11 : fst (lookup N11 γ) ≡ fst (numeralL 11))
  (numK2 : ⟨ fst (numeralL 2) ∈ fst (lookup K γ) ⟩)
  (numK3 : ⟨ fst (numeralL 3) ∈ fst (lookup K γ) ⟩)
  (numK4 : ⟨ fst (numeralL 4) ∈ fst (lookup K γ) ⟩)
  (numK5 : ⟨ fst (numeralL 5) ∈ fst (lookup K γ) ⟩)
  (numK8 : ⟨ fst (numeralL 8) ∈ fst (lookup K γ) ⟩)
  (numK9 : ⟨ fst (numeralL 9) ∈ fst (lookup K γ) ⟩)
  (numK10 : ⟨ fst (numeralL 10) ∈ fst (lookup K γ) ⟩)
  (numK11 : ⟨ fst (numeralL 11) ∈ fst (lookup K γ) ⟩)
  (innerK : (k : ℕ) (a : S) → ⟨ fst (prʟ (numeralL k) a) ∈ fst (lookup K γ) ⟩)
  (innerPairK : (k : ℕ) (a b : S) → ⟨ fst (prʟ (numeralL k) (prʟ a b)) ∈ fst (lookup K γ) ⟩)
  (pairK : (a b : S) → ⟨ fst (prʟ a b) ∈ fst (lookup K γ) ⟩)
  (codesK : (k : ℕ) → (c ar a b : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
           → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
           → ⟨ fst ar ∈ fst (lookup K γ) ⟩
             × ⟨ fst a ∈ fst (lookup K γ) ⟩ × ⟨ fst b ∈ fst (lookup K γ) ⟩)
  (unCodesK : (k : ℕ) → (c ar a : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
             → fst c ≡ pr (fst ar) (pr (# k) (fst a))
             → ⟨ fst ar ∈ fst (lookup K γ) ⟩ × ⟨ fst a ∈ fst (lookup K γ) ⟩)
  (entryK : (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst (lookup C γ) ⟩
           → ⟨ fst x ∈ fst (lookup K γ) ⟩ × ⟨ fst y ∈ fst (lookup K γ) ⟩) where

  module R2 = BothSameRel {n} C γ
  module R3 = BothSameRel {n} C γ
  module R4 = BothSameRel {n} C γ
  module R5 = OneSameRel {n} C γ
  module R8 = OneSuccRel {n} C K γ entryK
  module R9 = OneSuccRel {n} C K γ entryK
  module R10 = SuccSndRel {n} C K γ entryK
  module R11 = SuccSndRel {n} C K γ entryK

  module C2 = BinFrameAgree {n} C N2 K 2 γ tagEq2 numK2 (innerPairK 2) pairK
                (codesK 2) (bothSameB C) (bothSameAt C) R2.out R2.back
  module C3 = BinFrameAgree {n} C N3 K 3 γ tagEq3 numK3 (innerPairK 3) pairK
                (codesK 3) (bothSameB C) (bothSameAt C) R3.out R3.back
  module C4 = BinFrameAgree {n} C N4 K 4 γ tagEq4 numK4 (innerPairK 4) pairK
                (codesK 4) (bothSameB C) (bothSameAt C) R4.out R4.back
  module C5 = UnFrameAgree {n} C N5 K 5 γ tagEq5 numK5 (innerK 5)
                (unCodesK 5) (oneSameB C) (oneSameAt C) R5.out R5.back
  module C8 = UnFrameAgree {n} C N8 K 8 γ tagEq8 numK8 (innerK 8)
                (unCodesK 8) (oneSuccB C K) (oneSuccAt C) R8.back R8.out
  module C9 = UnFrameAgree {n} C N9 K 9 γ tagEq9 numK9 (innerK 9)
                (unCodesK 9) (oneSuccB C K) (oneSuccAt C) R9.back R9.out
  module C10 = BinFrameAgree {n} C N10 K 10 γ tagEq10 numK10 (innerPairK 10) pairK
                 (codesK 10) (succSndB C K) (succSndAt C) R10.back R10.out
  module C11 = BinFrameAgree {n} C N11 K 11 γ tagEq11 numK11 (innerPairK 11) pairK
                 (codesK 11) (succSndB C K) (succSndAt C) R11.back R11.out

  out : ⟨ γ ⊨ closedAt C ⟩ → ⟨ γ ⊨ closedBS C K N2 N3 N4 N5 N8 N9 N10 N11 ⟩
  out h =
    ( C2.out (h .fst)
    , ( C3.out (h .snd .fst)
      , ( C4.out (h .snd .snd .fst)
        , ( C5.out (h .snd .snd .snd .fst)
          , ( C8.out (h .snd .snd .snd .snd .fst)
            , ( C9.out (h .snd .snd .snd .snd .snd .fst)
              , ( C10.out (h .snd .snd .snd .snd .snd .snd .fst)
                , C11.out (h .snd .snd .snd .snd .snd .snd .snd) )))))))

  back : ⟨ γ ⊨ closedBS C K N2 N3 N4 N5 N8 N9 N10 N11 ⟩ → ⟨ γ ⊨ closedAt C ⟩
  back h =
    ( C2.back (h .fst)
    , ( C3.back (h .snd .fst)
      , ( C4.back (h .snd .snd .fst)
        , ( C5.back (h .snd .snd .snd .fst)
          , ( C8.back (h .snd .snd .snd .snd .fst)
            , ( C9.back (h .snd .snd .snd .snd .snd .fst)
              , ( C10.back (h .snd .snd .snd .snd .snd .snd .fst)
                , C11.back (h .snd .snd .snd .snd .snd .snd .snd) )))))))

-- =====================================================================
-- SECTION 5. THE DOMAIN TRANSFER.
-- domB f d K against domAt f d.  out (domAt -> domB) needs the entry
-- witnesses in K; back (domB -> domAt) needs every entry's components
-- and every domain element in K.  At the generic frame these memberships
-- are hypotheses (the graph frame supplies them through its own bounded
-- quantifiers and the leg-D site facts); without them the back direction
-- is false, which is the measured negative of [LJ-1.55]'s claim.
-- =====================================================================
module DomainAgree {n : ℕ} (f d K : Fin n) (γ : S ^ n)
  (entryK : (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst (lookup f γ) ⟩
           → ⟨ fst x ∈ fst (lookup K γ) ⟩ × ⟨ fst y ∈ fst (lookup K γ) ⟩)
  (domK : (x : S) → ⟨ fst x ∈ fst (lookup d γ) ⟩ → ⟨ fst x ∈ fst (lookup K γ) ⟩) where

  mem : (x y : S) → ⟨ (y ∷ x ∷ γ) ⊨ appAt (suc (suc f)) (suc zero) zero ⟩
      → ⟨ pr (fst x) (fst y) ∈ fst (lookup f γ) ⟩
  mem x y ap = subst ⟨_⟩ (appAt-adequate (suc (suc f)) (suc zero) zero
                 (y ∷ x ∷ γ)) ap

  out : ⟨ γ ⊨ domAt f d ⟩ → ⟨ γ ⊨ domB f d K ⟩
  out h = λ x xK →
      ( λ hx → h x .fst
          (PT.rec squash₁ (λ { (y , (_ , ap)) → ∣ y , ap ∣₁ }) hx) )
    , ( λ hx → PT.rec squash₁
          (λ { (y , ap) →
            ∣ y , ( entryK x y (mem x y ap) .snd , ap ) ∣₁ })
          (h x .snd hx) )

  back : ⟨ γ ⊨ domB f d K ⟩ → ⟨ γ ⊨ domAt f d ⟩
  back h x =
      ( λ hx → PT.rec (snd (fst x ∈ fst (lookup d γ))) go hx )
    , ( λ m → PT.rec squash₁
          (λ { (y , (yK , p)) → ∣ y , p ∣₁ })
          (h x (domK x m) .snd m) )
    where
    go : Σ[ y ∈ S ] ⟨ (y ∷ x ∷ γ) ⊨ appAt (suc (suc f)) (suc zero) zero ⟩
       → ⟨ fst x ∈ fst (lookup d γ) ⟩
    go (y , ap) = h x (entryK x y (mem x y ap) .fst) .fst
      ∣ y , ( entryK x y (mem x y ap) .snd , ap ) ∣₁

-- =====================================================================
-- SECTION 6. THE SHAPEDNESS ATOMS.
-- The bounded term shape isTmBS t A K N0 N1 (the cured master, with
-- the constant and variable branches) against the machine's isTmAt
-- term disjuncts, branch by branch.  The constant branch reads the
-- payload in the carrier A; the variable branch reads it in the arity
-- slot.  out is story -> machine; in' is machine -> story (needing the
-- payload-in-K site fact, which the graph frame supplies).
-- =====================================================================
module TmBranch {m : ℕ} (t : Fin (4 + m)) (tag : Fin m) (k : ℕ)
  (x : Fin (4 + m)) (K : Fin m) (γ : S ^ (4 + m))
  (tagEq : fst (lookup (suc (suc (suc (suc tag)))) γ) ≡ fst (numeralL k))
  (numK : ⟨ fst (numeralL k) ∈ fst (lookup (suc (suc (suc (suc K)))) γ) ⟩)
  (inK : (v : S) → ⟨ fst v ∈ fst (lookup x γ) ⟩
         → ⟨ fst v ∈ fst (lookup (suc (suc (suc (suc K)))) γ) ⟩) where

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

  in' : ⟨ γ ⊨ machine ⟩ → ⟨ γ ⊨ story ⟩
  in' h = PT.rec squash₁ go h
    where
    go : Σ[ v ∈ S ] ⟨ (v ∷ γ) ⊨ tagAtL (suc t) k zero
                         ∧̇ (var zero ∈̇ var (suc x)) ⟩
       → ⟨ γ ⊨ story ⟩
    go (v , (hTag , vx)) = ∣ v , ( inK v (vx-raw) , ( hTagB , vx ) ) ∣₁
      where
      vx-raw : ⟨ fst v ∈ fst (lookup x γ) ⟩
      vx-raw = vx
      hTagB : ⟨ (v ∷ γ) ⊨ tagBS (suc t) (suc (suc (suc (suc (suc tag))))) zero
                                  (suc (suc (suc (suc (suc K))))) ⟩
      hTagB = ∣ numeralL k , ( numK , ( sym tagEq , tagPart ) ) ∣₁
        where
        tz' : fst (lookup (suc t) (v ∷ γ)) ≡ pr (# k) (fst (lookup zero (v ∷ γ)))
        tz' = subst ⟨_⟩ (tagAtL-adequate (suc t) k zero (v ∷ γ)) hTag
        tagPart : ⟨ (numeralL k ∷ v ∷ γ) ⊨ prAtL (suc (suc t)) zero (suc zero) ⟩
        tagPart = transport (cong fst (sym (prAtL-adequate (suc (suc t)) zero
                    (suc zero) (numeralL k ∷ v ∷ γ))))
          (tz' ∙ cong₂ pr (sym (numeralL-fst k)) refl)

module TmAgree {m : ℕ} (t : Fin (4 + m)) (A K N0 N1 : Fin m) (γ : S ^ (4 + m))
  (tagEq0 : fst (lookup (suc (suc (suc (suc N0)))) γ) ≡ fst (numeralL 0))
  (tagEq1 : fst (lookup (suc (suc (suc (suc N1)))) γ) ≡ fst (numeralL 1))
  (numK0 : ⟨ fst (numeralL 0) ∈ fst (lookup (suc (suc (suc (suc K)))) γ) ⟩)
  (numK1 : ⟨ fst (numeralL 1) ∈ fst (lookup (suc (suc (suc (suc K)))) γ) ⟩)
  (carrierK : (v : S) → ⟨ fst v ∈ fst (lookup (suc (suc (suc (suc A)))) γ) ⟩
             → ⟨ fst v ∈ fst (lookup (suc (suc (suc (suc K)))) γ) ⟩)
  (arityK : (v : S) → ⟨ fst v ∈ fst (lookup (suc (suc zero)) γ) ⟩
             → ⟨ fst v ∈ fst (lookup (suc (suc (suc (suc K)))) γ) ⟩) where

  module B0 = TmBranch {m} t N0 0 (suc (suc (suc (suc A)))) K γ
               tagEq0 numK0 carrierK
  module B1 = TmBranch {m} t N1 1 (suc (suc zero)) K γ
               tagEq1 numK1 arityK

  out : ⟨ γ ⊨ isTmBS t A K N0 N1 ⟩ → ⟨ γ ⊨ isTmAt t (suc (suc zero)) (suc (suc (suc (suc A)))) ⟩
  out h = PT.rec squash₁
    (λ { (inl h0) → ∣ inl (B0.out h0) ∣₁
       ; (inr h1) → ∣ inr (B1.out h1) ∣₁ })
    h

  in' : ⟨ γ ⊨ isTmAt t (suc (suc zero)) (suc (suc (suc (suc A)))) ⟩
      → ⟨ γ ⊨ isTmBS t A K N0 N1 ⟩
  in' h = PT.rec squash₁
    (λ { (inl h0) → ∣ inl (B0.in' h0) ∣₁
       ; (inr h1) → ∣ inr (B1.in' h1) ∣₁ })
    h

-- The measured negative behind the pre-cure isTmBS: the machine's two
-- term branches are disjoint (the tag numerals differ), so a machine
-- witness in the variable branch has no image in a constant-only story
-- shape.  This is the constructor [LJ-1.55]'s shapedness transfer could
-- not supply; the cure adds the variable branch.
module ConstVarDisjoint {m : ℕ} (t : Fin (4 + m)) (N A : Fin (4 + m))
  (γ : S ^ (4 + m)) where

  disj : ⟨ γ ⊨ ∃̇ (tagAtL (suc t) 0 zero ∧̇ (var zero ∈̇ var (suc A))) ⟩
       → ⟨ γ ⊨ ∃̇ (tagAtL (suc t) 1 zero ∧̇ (var zero ∈̇ var (suc N))) ⟩
       → Empty.⊥
  disj h0 h1 = PT.rec Empty.isProp⊥ go0 h0
    where
    go0 : Σ[ v ∈ S ] ⟨ (v ∷ γ) ⊨ tagAtL (suc t) 0 zero ∧̇ (var zero ∈̇ var (suc A)) ⟩
        → Empty.⊥
    go0 (v , (h0t , _)) = PT.rec Empty.isProp⊥ go1 h1
      where
      go1 : Σ[ z ∈ S ] ⟨ (z ∷ γ) ⊨ tagAtL (suc t) 1 zero ∧̇ (var zero ∈̇ var (suc N)) ⟩
          → Empty.⊥
      go1 (z , (h1t , _)) = inj (#-inj′ (pr-inj (sym e0 ∙ e1) .fst))
        where
        e0 : fst (lookup (suc t) (v ∷ γ)) ≡ pr (# 0) (fst v)
        e0 = transport (cong fst (tagAtL-adequate (suc t) 0 zero (v ∷ γ))) h0t
        e1 : fst (lookup (suc t) (z ∷ γ)) ≡ pr (# 1) (fst z)
        e1 = transport (cong fst (tagAtL-adequate (suc t) 1 zero (z ∷ γ))) h1t
        inj : 0 ≡ 1 → Empty.⊥
        inj p = subst (λ { zero → Unit ; (suc _) → Empty.⊥ }) p tt

-- =====================================================================
-- SECTION 7. SatGraphAgree AT THE GRAPH FRAME.
-- SatGraphB.satGraphB w K Ns ts against satGraphAt (sh3 w) (suc zero)
-- zero at the 8-deep environment, composing TwelveAgree (parameters),
-- ClosedAgree, DomainAgree, the pin/appAt identities and the three
-- existential-frame transfers.  The story's closedness slot is the
-- code set (the [LJ-1.56] cure); the machine's witness memberships in
-- K are the witK site fact.
-- =====================================================================
module SatGraphAgree {n : ℕ} (w K : Fin (5 + n))
  (N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 : Fin (5 + n))
  (γ : S ^ (8 + n))
  (twelve-out : (d e f : S) → ⟨ (f ∷ e ∷ d ∷ γ) ⊨ twelveAt (suc (suc zero)) (suc zero) zero ⟩
              → ⟨ (f ∷ e ∷ d ∷ γ) ⊨ SatGraphB.twelveB {n} w K N0 N1 N2 N3 N4 N5
                                          N6 N7 N8 N9 N10 N11 t0 t1 ⟩)
  (twelve-back : (d e f : S) → ⟨ (f ∷ e ∷ d ∷ γ) ⊨ SatGraphB.twelveB {n} w K N0 N1 N2 N3 N4 N5
                                           N6 N7 N8 N9 N10 N11 t0 t1 ⟩
               → ⟨ (f ∷ e ∷ d ∷ γ) ⊨ twelveAt (suc (suc zero)) (suc zero) zero ⟩)
  -- the closedness site facts at the graph frame (C = slot 2, K = the
  -- K slot of the 5-deep env, the tag slots of the 5-deep env)
  (tagEq2 : fst (lookup (suc (suc (suc N2))) γ) ≡ fst (numeralL 2))
  (tagEq3 : fst (lookup (suc (suc (suc N3))) γ) ≡ fst (numeralL 3))
  (tagEq4 : fst (lookup (suc (suc (suc N4))) γ) ≡ fst (numeralL 4))
  (tagEq5 : fst (lookup (suc (suc (suc N5))) γ) ≡ fst (numeralL 5))
  (tagEq8 : fst (lookup (suc (suc (suc N8))) γ) ≡ fst (numeralL 8))
  (tagEq9 : fst (lookup (suc (suc (suc N9))) γ) ≡ fst (numeralL 9))
  (tagEq10 : fst (lookup (suc (suc (suc N10))) γ) ≡ fst (numeralL 10))
  (tagEq11 : fst (lookup (suc (suc (suc N11))) γ) ≡ fst (numeralL 11))
  (numK2 : ⟨ fst (numeralL 2) ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (numK3 : ⟨ fst (numeralL 3) ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (numK4 : ⟨ fst (numeralL 4) ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (numK5 : ⟨ fst (numeralL 5) ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (numK8 : ⟨ fst (numeralL 8) ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (numK9 : ⟨ fst (numeralL 9) ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (numK10 : ⟨ fst (numeralL 10) ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (numK11 : ⟨ fst (numeralL 11) ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (innerK : (k : ℕ) (a : S) → ⟨ fst (prʟ (numeralL k) a) ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (innerPairK : (k : ℕ) (a b : S) → ⟨ fst (prʟ (numeralL k) (prʟ a b)) ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (pairK : (a b : S) → ⟨ fst (prʟ a b) ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (codesK : (d e f : S) → (k : ℕ) → (c ar a b : S) → ⟨ fst c ∈ fst (lookup (suc (suc zero)) (f ∷ e ∷ d ∷ γ)) ⟩
           → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
           → ⟨ fst ar ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
             × ⟨ fst a ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
             × ⟨ fst b ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (unCodesK : (d e f : S) → (k : ℕ) → (c ar a : S) → ⟨ fst c ∈ fst (lookup (suc (suc zero)) (f ∷ e ∷ d ∷ γ)) ⟩
             → fst c ≡ pr (fst ar) (pr (# k) (fst a))
             → ⟨ fst ar ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
               × ⟨ fst a ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (closedEntryK : (d e f : S) → (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst (lookup (suc (suc zero)) (f ∷ e ∷ d ∷ γ)) ⟩
                  → ⟨ fst x ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
                    × ⟨ fst y ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  -- the domain facts on the table (slot 1) and the domain set (slot 2)
  (domEntryK : (d e f : S) → (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst (lookup (suc zero) (f ∷ e ∷ d ∷ γ)) ⟩
               → ⟨ fst x ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
                 × ⟨ fst y ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (domK : (d e f : S) → (x : S) → ⟨ fst x ∈ fst (lookup (suc (suc zero)) (f ∷ e ∷ d ∷ γ)) ⟩
          → ⟨ fst x ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  -- the machine witnesses lie in K (the graph frame's bounded
  -- quantifiers supply the memberships)
  (witK : (d e f : S) → ⟨ (f ∷ e ∷ d ∷ γ) ⊨
             (var zero ≐ var (suc (suc (suc (suc (suc (suc w)))))))
             ∧̇ (closedAt (suc (suc zero))
               ∧̇ (domAt (suc zero) (suc (suc zero))
                 ∧̇ (appAt (suc zero) (suc (suc (suc (suc zero))))
                            (suc (suc (suc zero)))
                   ∧̇ twelveAt (suc (suc zero)) (suc zero) zero))) ⟩
         → ⟨ fst d ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
           × ⟨ fst e ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
           × ⟨ fst f ∈ fst (lookup (suc (suc (suc K))) γ) ⟩) where

  body-out : (d e f : S) → ⟨ (f ∷ e ∷ d ∷ γ) ⊨
               (var zero ≐ var (suc (suc (suc (suc (suc (suc w)))))))
               ∧̇ (closedAt (suc (suc zero))
                 ∧̇ (domAt (suc zero) (suc (suc zero))
                   ∧̇ (appAt (suc zero) (suc (suc (suc (suc zero))))
                              (suc (suc (suc zero)))
                     ∧̇ twelveAt (suc (suc zero)) (suc zero) zero))) ⟩
           → ⟨ (f ∷ e ∷ d ∷ γ) ⊨
               (var zero ≐ var (suc (suc (suc (suc (suc (suc w)))))))
               ∧̇ (closedBS (suc (suc zero))
                     (suc (suc (suc (suc (suc (suc K))))))
                     (suc (suc (suc (suc (suc (suc N2))))))
                     (suc (suc (suc (suc (suc (suc N3))))))
                     (suc (suc (suc (suc (suc (suc N4))))))
                     (suc (suc (suc (suc (suc (suc N5))))))
                     (suc (suc (suc (suc (suc (suc N8))))))
                     (suc (suc (suc (suc (suc (suc N9))))))
                     (suc (suc (suc (suc (suc (suc N10))))))
                     (suc (suc (suc (suc (suc (suc N11))))))
                 ∧̇ (domB (suc zero) (suc (suc zero))
                        (suc (suc (suc (suc (suc (suc K))))))
                   ∧̇ (appAt (suc zero) (suc (suc (suc (suc zero))))
                              (suc (suc (suc zero)))
                     ∧̇ SatGraphB.twelveB {n} w K N0 N1 N2 N3 N4 N5
                                          N6 N7 N8 N9 N10 N11 t0 t1))) ⟩
  body-out d e f h = ( h .fst
                     , ( CA.out (h .snd .fst)
                       , ( DA.out (h .snd .snd .fst)
                         , ( h .snd .snd .snd .fst
                           , twelve-out d e f (h .snd .snd .snd .snd) ) ) ) )
    where
    module CA = ClosedAgree {11 + n} (suc (suc zero))
                  (suc (suc (suc (suc (suc (suc K))))))
                  (suc (suc (suc (suc (suc (suc N2))))))
                  (suc (suc (suc (suc (suc (suc N3))))))
                  (suc (suc (suc (suc (suc (suc N4))))))
                  (suc (suc (suc (suc (suc (suc N5))))))
                  (suc (suc (suc (suc (suc (suc N8))))))
                  (suc (suc (suc (suc (suc (suc N9))))))
                  (suc (suc (suc (suc (suc (suc N10))))))
                  (suc (suc (suc (suc (suc (suc N11)))))) (f ∷ e ∷ d ∷ γ)
                  tagEq2 tagEq3 tagEq4 tagEq5 tagEq8 tagEq9 tagEq10 tagEq11
                  numK2 numK3 numK4 numK5 numK8 numK9 numK10 numK11
                  innerK innerPairK pairK (codesK d e f) (unCodesK d e f)
                  (closedEntryK d e f)
    module DA = DomainAgree {11 + n} (suc zero) (suc (suc zero))
                  (suc (suc (suc (suc (suc (suc K)))))) (f ∷ e ∷ d ∷ γ)
                  (domEntryK d e f) (domK d e f)

  body-back : (d e f : S) → ⟨ (f ∷ e ∷ d ∷ γ) ⊨
                (var zero ≐ var (suc (suc (suc (suc (suc (suc w)))))))
                ∧̇ (closedBS (suc (suc zero))
                      (suc (suc (suc (suc (suc (suc K))))))
                      (suc (suc (suc (suc (suc (suc N2))))))
                      (suc (suc (suc (suc (suc (suc N3))))))
                      (suc (suc (suc (suc (suc (suc N4))))))
                      (suc (suc (suc (suc (suc (suc N5))))))
                      (suc (suc (suc (suc (suc (suc N8))))))
                      (suc (suc (suc (suc (suc (suc N9))))))
                      (suc (suc (suc (suc (suc (suc N10))))))
                      (suc (suc (suc (suc (suc (suc N11))))))
                  ∧̇ (domB (suc zero) (suc (suc zero))
                         (suc (suc (suc (suc (suc (suc K))))))
                    ∧̇ (appAt (suc zero) (suc (suc (suc (suc zero))))
                               (suc (suc (suc zero)))
                      ∧̇ SatGraphB.twelveB {n} w K N0 N1 N2 N3 N4 N5
                                           N6 N7 N8 N9 N10 N11 t0 t1))) ⟩
            → ⟨ (f ∷ e ∷ d ∷ γ) ⊨
                (var zero ≐ var (suc (suc (suc (suc (suc (suc w)))))))
                ∧̇ (closedAt (suc (suc zero))
                  ∧̇ (domAt (suc zero) (suc (suc zero))
                    ∧̇ (appAt (suc zero) (suc (suc (suc (suc zero))))
                               (suc (suc (suc zero)))
                      ∧̇ twelveAt (suc (suc zero)) (suc zero) zero))) ⟩
  body-back d e f h = ( h .fst
                      , ( CA.back (h .snd .fst)
                        , ( DA.back (h .snd .snd .fst)
                          , ( h .snd .snd .snd .fst
                            , twelve-back d e f (h .snd .snd .snd .snd) ) ) ) )
    where
    module CA = ClosedAgree {11 + n} (suc (suc zero))
                  (suc (suc (suc (suc (suc (suc K))))))
                  (suc (suc (suc (suc (suc (suc N2))))))
                  (suc (suc (suc (suc (suc (suc N3))))))
                  (suc (suc (suc (suc (suc (suc N4))))))
                  (suc (suc (suc (suc (suc (suc N5))))))
                  (suc (suc (suc (suc (suc (suc N8))))))
                  (suc (suc (suc (suc (suc (suc N9))))))
                  (suc (suc (suc (suc (suc (suc N10))))))
                  (suc (suc (suc (suc (suc (suc N11)))))) (f ∷ e ∷ d ∷ γ)
                  tagEq2 tagEq3 tagEq4 tagEq5 tagEq8 tagEq9 tagEq10 tagEq11
                  numK2 numK3 numK4 numK5 numK8 numK9 numK10 numK11
                  innerK innerPairK pairK (codesK d e f) (unCodesK d e f)
                  (closedEntryK d e f)
    module DA = DomainAgree {11 + n} (suc zero) (suc (suc zero))
                  (suc (suc (suc (suc (suc (suc K)))))) (f ∷ e ∷ d ∷ γ)
                  (domEntryK d e f) (domK d e f)

  sh3 : ∀ {m} → Fin m → Fin (3 + m)
  sh3 i = suc (suc (suc i))

  out : ⟨ γ ⊨ satGraphAt (sh3 w) (suc zero) zero ⟩
      → ⟨ γ ⊨ SatGraphB.satGraphB w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 ⟩
  out h = PT.rec squash₁
    (λ { (d , hT) → PT.rec squash₁
      (λ { (e , hb) → PT.rec squash₁
        (λ { (f , body) →
          let ks = witK d e f body
          in ∣ d , ( ks .fst
                   , ∣ e , ( ks .snd .fst
                           , ∣ f , ( ks .snd .snd , body-out d e f body ) ∣₁ )
                     ∣₁ ) ∣₁ })
        hb })
      hT })
    h

  back : ⟨ γ ⊨ SatGraphB.satGraphB w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 ⟩
       → ⟨ γ ⊨ satGraphAt (sh3 w) (suc zero) zero ⟩
  back h = PT.rec squash₁
    (λ { (d , (dK , hT)) → PT.rec squash₁
      (λ { (e , (eK , hb)) → PT.rec squash₁
        (λ { (f , (fK , body)) →
          ∣ d , ∣ e , ∣ f , body-back d e f body ∣₁ ∣₁ ∣₁ })
        hb })
      hT })
    h

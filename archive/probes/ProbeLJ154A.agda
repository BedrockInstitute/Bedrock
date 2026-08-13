{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.54] probe A: the leaf-reduction atoms.
--
-- The residual of [LJ-1.53] is the two-way `DefBodyB`/`DefBody`
-- satisfaction transfer at the leaf environment under the site facts.
-- Its pieces decompose as isCodeBS <-> isCodeAt, SatGraphB.satGraphB
-- <-> satGraphAt (the twelve rows compose), and DefinesBS <-> DefinesAt.
-- This probe builds the atoms the composition is made of: the tag
-- transfer, the key-arity transfer, the one-entry-environment transfer,
-- and the Defines transfer.  The twelve-row composition and the
-- satGraph composition are the long pole and are stated as the terms
-- not yet written (C-36).
--
-- Untracked probe; never committed.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ154A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

import FOL.Absoluteness
open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _∧̇_; ∃̇_; ∃̇∈; _∈̇_; _≐_ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )
open import L.Coding.Model {ℓ}
  using ( prAtL; tagAtL; tagAtL-adequate; prAtL-adequate; extAt )
open import L.Coding.Powerset {ℓ} lem using ( envOneAt; DefinesAt )
open import L.Coding.CodeSet {ℓ} lem using ( keyArityAtL )
open import L.Condensation {ℓ} lem using
  ( tagBS; keyArBS; envOneBndS; DefinesBS
  ; extAtB→extAt; extAt→extAtB )

import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )
open import Cubical.Data.Vec using ( map )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

private
  PairIs : V ℓ → V ℓ → Ω
  PairIs a p = (a ≡ p) , setIsSet a p

-- =====================================================================
-- THE TAG TRANSFER.  tagBS s tag x K = "exists t in K: t is the tag
-- slot and the s-slot is the pair (t, x-slot)".  tagAtL s k x =
-- "exists t: t = #k and the s-slot is the pair (t, x-slot)".  The two
-- agree when the tag slot holds the numeral #k and the numeral lies in
-- K.
-- =====================================================================
module TagAgree {n : ℕ} (s tag x K : Fin n) (γ : S ^ n) (k : ℕ)
  (tagEq : fst (lookup tag γ) ≡ fst (numeralL k))
  (numK : ⟨ fst (numeralL k) ∈ fst (lookup K γ) ⟩) where

  out : ⟨ γ ⊨ tagAtL s k x ⟩ → ⟨ γ ⊨ tagBS s tag x K ⟩
  out h = ∣ numeralL k , ( numK , ( sym tagEq , hp ) ) ∣₁
    where
    h' : ⟨ PairIs (fst (lookup s γ)) (pr (fst (numeralL k)) (fst (lookup x γ))) ⟩
    h' = subst ⟨_⟩
           (cong (λ w → PairIs (fst (lookup s γ)) (pr w (fst (lookup x γ))))
             (sym (numeralL-fst k)))
           (subst ⟨_⟩ (tagAtL-adequate s k x γ) h)
    hp : ⟨ (numeralL k ∷ γ) ⊨ prAtL (suc s) zero (suc x) ⟩
    hp = subst ⟨_⟩ (sym (prAtL-adequate {suc n} (suc s) zero (suc x) (numeralL k ∷ γ))) h'

  back : ⟨ γ ⊨ tagBS s tag x K ⟩ → ⟨ γ ⊨ tagAtL s k x ⟩
  back h = subst ⟨_⟩ (sym (tagAtL-adequate s k x γ))
    (subst (λ u → fst (lookup s γ) ≡ pr u (fst (lookup x γ)))
      (numeralL-fst k) go)
    where
    go : fst (lookup s γ) ≡ pr (fst (numeralL k)) (fst (lookup x γ))
    go = PT.rec (snd (PairIs (fst (lookup s γ))
                       (pr (fst (numeralL k)) (fst (lookup x γ)))))
      (λ { (t , (tK , (te , tp))) →
        subst (λ u → fst (lookup s γ) ≡ pr u (fst (lookup x γ)))
          (te ∙ tagEq)
          (subst ⟨_⟩ (prAtL-adequate {suc n} (suc s) zero (suc x) (t ∷ γ)) tp) })
      h

-- =====================================================================
-- THE KEY-ARITY TRANSFER.  keyArBS c tag K = "exists t ar in K: ar is
-- the tag slot and the c-slot is the pair (ar, t)".  keyArityAtL c k =
-- "exists t: the c-slot is the pair (#k, t)".  The two agree when the
-- tag slot holds #k, the numeral lies in K, and the machine's key
-- value lies in K.
-- =====================================================================
module KeyAgree {n : ℕ} (c tag K : Fin n) (γ : S ^ n) (k : ℕ)
  (tagEq : fst (lookup tag γ) ≡ fst (numeralL k))
  (numK : ⟨ fst (numeralL k) ∈ fst (lookup K γ) ⟩)
  (keyValK : (t : S) → ⟨ (t ∷ γ) ⊨ tagAtL (suc c) k zero ⟩
            → ⟨ fst t ∈ fst (lookup K γ) ⟩) where

  out : ⟨ γ ⊨ keyArityAtL c k ⟩ → ⟨ γ ⊨ keyArBS c tag K ⟩
  out h = PT.rec squash₁ go h
    where
    go : Σ[ t ∈ S ] ⟨ (t ∷ γ) ⊨ tagAtL (suc c) k zero ⟩
       → ⟨ γ ⊨ keyArBS c tag K ⟩
    go (t , ht) = ∣ t , ( keyValK t ht
        , ∣ numeralL k
            , ( numK , ( te' , hp ) ) ∣₁ ) ∣₁
      where
      te' : ⟨ (numeralL k ∷ t ∷ γ) ⊨ var zero ≐ var (suc (suc tag)) ⟩
      te' = sym tagEq
      hp : ⟨ (numeralL k ∷ t ∷ γ) ⊨ prAtL (suc (suc c)) zero (suc zero) ⟩
      hp = subst ⟨_⟩ (sym (prAtL-adequate {suc (suc n)} (suc (suc c)) zero (suc zero)
             (numeralL k ∷ t ∷ γ)))
        (subst (λ u → fst (lookup (suc (suc c)) (numeralL k ∷ t ∷ γ)) ≡ pr u (fst t))
          (sym (numeralL-fst k))
          (subst ⟨_⟩ (tagAtL-adequate (suc c) k zero (t ∷ γ)) ht))

  back : ⟨ γ ⊨ keyArBS c tag K ⟩ → ⟨ γ ⊨ keyArityAtL c k ⟩
  back h = PT.rec squash₁ go h
    where
    go : Σ[ t ∈ S ] (⟨ fst t ∈ fst (lookup K γ) ⟩
                    × ∥ Σ[ ar ∈ S ] (⟨ fst ar ∈ fst (lookup K γ) ⟩
                        × ⟨ (ar ∷ t ∷ γ) ⊨
                             ((var zero ≐ var (suc (suc tag)))
                              ∧̇ prAtL (suc (suc c)) zero (suc zero)) ⟩) ∥₁)
       → ⟨ γ ⊨ keyArityAtL c k ⟩
    go (t , tK , hw) = PT.rec squash₁ go₂ hw
      where
      go₂ : Σ[ ar ∈ S ] (⟨ fst ar ∈ fst (lookup K γ) ⟩
                        × ⟨ (ar ∷ t ∷ γ) ⊨
                             ((var zero ≐ var (suc (suc tag)))
                              ∧̇ prAtL (suc (suc c)) zero (suc zero)) ⟩)
          → ⟨ γ ⊨ keyArityAtL c k ⟩
      go₂ (ar , arK , (ae , ap)) =
        ∣ t , subst ⟨_⟩ (sym (tagAtL-adequate (suc c) k zero (t ∷ γ)))
              (subst (λ w → fst (lookup (suc c) (t ∷ γ)) ≡ pr w (fst (lookup zero (t ∷ γ))))
                (numeralL-fst k)
                (subst (λ u → fst (lookup (suc (suc c)) (ar ∷ t ∷ γ)) ≡ pr u (fst t))
                  (ae ∙ tagEq)
                  (subst ⟨_⟩ (prAtL-adequate {suc (suc n)} (suc (suc c)) zero (suc zero)
                    (ar ∷ t ∷ γ)) ap))) ∣₁


-- =====================================================================
-- THE ONE-ENTRY-ENVIRONMENT TRANSFER.  envOneBndS v K N0 at
-- E ∷ x' ∷ γ = "the set at E is exactly the satisfiers of tagBS in K",
-- envOneAt zero (suc zero) = "the set at E is exactly the satisfiers
-- of tagAtL".  The two agree when the N0 slot holds #0, the numeral
-- lies in K, and every machine satisfier lies in K.
-- =====================================================================
module EnvOneAgree {m : ℕ} (v K N0 : Fin m) (γ : S ^ (2 + m))
  (N0eq : fst (lookup (suc (suc N0)) γ) ≡ fst (numeralL 0))
  (numK : ⟨ fst (numeralL 0) ∈ fst (lookup (suc (suc K)) γ) ⟩)
  (pairK : (z : S) → ⟨ (z ∷ γ) ⊨ tagAtL zero 0 (suc (suc zero)) ⟩
          → ⟨ fst z ∈ fst (lookup (suc (suc K)) γ) ⟩) where

  φB : Formula S (3 + m)
  φB = tagBS zero (suc (suc (suc N0))) (suc (suc zero)) (suc (suc (suc K)))

  φ : Formula S (3 + m)
  φ = tagAtL zero 0 (suc (suc zero))

  fwd : (z : S) → ⟨ (z ∷ γ) ⊨ φB ⟩ → ⟨ (z ∷ γ) ⊨ φ ⟩
  fwd z = T.back
    where
    module T = TagAgree {3 + m} zero (suc (suc (suc N0))) (suc (suc zero))
      (suc (suc (suc K))) (z ∷ γ) 0 N0eq numK

  bwd : (z : S) → ⟨ (z ∷ γ) ⊨ φ ⟩ → ⟨ (z ∷ γ) ⊨ φB ⟩
  bwd z = T.out
    where
    module T = TagAgree {3 + m} zero (suc (suc (suc N0))) (suc (suc zero))
      (suc (suc (suc K))) (z ∷ γ) 0 N0eq numK

  out : ⟨ γ ⊨ envOneAt zero (suc zero) ⟩ → ⟨ γ ⊨ envOneBndS v K N0 ⟩
  out = extAt→extAtB zero (suc (suc K)) φB φ γ fwd bwd

  back : ⟨ γ ⊨ envOneBndS v K N0 ⟩ → ⟨ γ ⊨ envOneAt zero (suc zero) ⟩
  back = extAtB→extAt zero (suc (suc K)) φB φ γ fwd bwd pairK

-- =====================================================================
-- THE DEFINES TRANSFER.  DefinesBS x w v K N0 at γ = "the set at x is
-- exactly the z in w with a K-bounded one-entry environment E with z
-- in v"; DefinesAt x w v is the same with the bounds removed.  The
-- two agree when the N0 slot holds #0, the numeral and every
-- one-entry environment lie in K, and the machine satisfiers lie in
-- K.
-- =====================================================================
module DefinesAgree {m : ℕ} (x w v K N0 : Fin m) (γ : S ^ m)
  (N0eq : fst (lookup N0 γ) ≡ fst (numeralL 0))
  (numK : ⟨ fst (numeralL 0) ∈ fst (lookup K γ) ⟩)
  (envK : (E z : S) → ⟨ (E ∷ z ∷ γ) ⊨ envOneAt zero (suc zero) ⟩
         → ⟨ fst E ∈ fst (lookup K γ) ⟩)
  (pairK : (E z w' : S) → ⟨ (w' ∷ E ∷ z ∷ γ) ⊨ tagAtL zero 0 (suc (suc zero)) ⟩
          → ⟨ fst w' ∈ fst (lookup K γ) ⟩)
  (satK : (z : S) → ⟨ (z ∷ γ) ⊨
             ((var zero ∈̇ var (suc w)) ∧̇
              ∃̇ (envOneAt zero (suc zero) ∧̇ (var zero ∈̇ var (suc (suc v))))) ⟩
         → ⟨ fst z ∈ fst (lookup K γ) ⟩) where

  bodyB : Formula S (suc m)
  bodyB = (var zero ∈̇ var (suc w))
          ∧̇ ∃̇∈ (var (suc K)) (envOneBndS v K N0 ∧̇ (var zero ∈̇ var (suc (suc v))))

  bodyM : Formula S (suc m)
  bodyM = (var zero ∈̇ var (suc w))
          ∧̇ ∃̇ (envOneAt zero (suc zero) ∧̇ (var zero ∈̇ var (suc (suc v))))

  fwd : (z : S) → ⟨ (z ∷ γ) ⊨ bodyB ⟩ → ⟨ (z ∷ γ) ⊨ bodyM ⟩
  fwd z (hz , hx) = hz , PT.rec squash₁ go hx
    where
    go : Σ[ E ∈ S ] (⟨ fst E ∈ fst (lookup K γ) ⟩
                    × ⟨ (E ∷ z ∷ γ) ⊨ envOneBndS v K N0
                         ∧̇ (var zero ∈̇ var (suc (suc v))) ⟩)
       → ⟨ (z ∷ γ) ⊨ ∃̇ (envOneAt zero (suc zero) ∧̇ (var zero ∈̇ var (suc (suc v)))) ⟩
    go (E , (EK , hE)) = ∣ E , ( eOne , hE .snd ) ∣₁
      where
      eOne : ⟨ (E ∷ z ∷ γ) ⊨ envOneAt zero (suc zero) ⟩
      eOne = EA.back (hE .fst)
        where
        module EA = EnvOneAgree {m} v K N0 (E ∷ z ∷ γ) N0eq numK
          (λ w' hw → pairK E z w' hw)

  bwd : (z : S) → ⟨ (z ∷ γ) ⊨ bodyM ⟩ → ⟨ (z ∷ γ) ⊨ bodyB ⟩
  bwd z (hz , hx) = hz , PT.rec squash₁ go hx
    where
    go : Σ[ E ∈ S ] ⟨ (E ∷ z ∷ γ) ⊨ envOneAt zero (suc zero)
                         ∧̇ (var zero ∈̇ var (suc (suc v))) ⟩
       → ⟨ (z ∷ γ) ⊨ ∃̇∈ (var (suc K))
             (envOneBndS v K N0 ∧̇ (var zero ∈̇ var (suc (suc v)))) ⟩
    go (E , (hE , hv)) = ∣ E , ( envK E z hE , ( eB , hv ) ) ∣₁
      where
      eB : ⟨ (E ∷ z ∷ γ) ⊨ envOneBndS v K N0 ⟩
      eB = EA.out hE
        where
        module EA = EnvOneAgree {m} v K N0 (E ∷ z ∷ γ) N0eq numK
          (λ w' hw → pairK E z w' hw)

  out : ⟨ γ ⊨ DefinesAt x w v ⟩ → ⟨ γ ⊨ DefinesBS x w v K N0 ⟩
  out = extAt→extAtB x K bodyB bodyM γ fwd bwd

  back : ⟨ γ ⊨ DefinesBS x w v K N0 ⟩ → ⟨ γ ⊨ DefinesAt x w v ⟩
  back = extAtB→extAt x K bodyB bodyM γ fwd bwd satK

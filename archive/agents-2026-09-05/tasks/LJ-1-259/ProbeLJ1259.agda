{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.259] probe: the env closure, the one L-row nobody priced.
--
-- [LJ-1.258] named C-36's missing hypothesis for the three consK-*
-- fields:
--
--   envConsK : {k} (g : Fin k → V ℓ) (x : V ℓ)
--            → env g ∈ K → x ∈ K → env (cons x g) ∈ K
--
-- This probe MEASURES that the term does NOT build over (K, Ktr)
-- alone, and DOES build tower-neutral over (K, Ktr) plus ONE new
-- hypothesis, the finite-gather closure finSetK, plus the four
-- closures the master already carries (numK0, sucK, pairK, transK
-- from Ktr).  finSetK is the second unpriced L-row.
--
-- ONE agda process, GHCRTS="-A64m -I0 -M8g", cap never raised.
-- Never committed.  Written incrementally (C-22).

open import Base.Prelude
open import Base.Truth

module LJ-1-259.ProbeLJ1259 {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _∈̇_; _∧̇_ )
open import FOL.Semantics using ( _^_ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; isTransV; Lset; Lset-layer; layer-trans )
open import L.Axioms.Basic {ℓ} using ( isL-Lset; finSet )
open import L.Coding.Model {ℓ}
  using ( consAtL; consAtL-adequate )
open import L.Coding.Environment {ℓ} using ( env; cons )

open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆; ⁅_⁆s; pairing-ax; module InfinitySet )
open InfinitySet using ( #_; sucV )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ∈∈ₛ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
import Cubical.Data.Sum as Sum
open Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Nat using ( ℕ )
open import Cubical.Data.FinData using ( Fin; toℕ )
open import Cubical.Data.Vec using ( Vec; lookup )

pattern one   = suc zero
pattern two   = suc one
pattern three = suc two
pattern four  = suc three
pattern five  = suc four
pattern six   = suc five
pattern seven = suc six
pattern eight = suc seven
pattern nine  = suc eight

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _⊨ᵐ_ )

-- ===================================================================
-- The env closure, stated over the structure (K, Ktr).  No tower is
-- named (DD4).
-- ===================================================================

module Fact (K : S) (Ktr : isTransV (fst K)) where

  -- A transitive set absorbs both components of a Kuratowski pair it
  -- contains ([LJ-1.151] ProbeLJ1151A.agda:58-71, green).
  prK : (x y : V ℓ) → ⟨ pr x y ∈ fst K ⟩ → ⟨ x ∈ fst K ⟩ × ⟨ y ∈ fst K ⟩
  prK x y h = Ktr (mem x (inl refl)) pairInK , Ktr (mem y (inr refl)) pairInK
    where
    pairInK : ⟨ ⁅ x , y ⁆ ∈ fst K ⟩
    pairInK = Ktr (∈∈ₛ {a = ⁅ x , y ⁆} {b = pr x y} .snd
                (pairing-ax ⁅ x ⁆s ⁅ x , y ⁆ ⁅ x , y ⁆ .snd ∣ inr refl ∣₁)) h
    mem : (z : V ℓ) → (z ≡ x) Sum.⊎ (z ≡ y) → ⟨ z ∈ ⁅ x , y ⁆ ⟩
    mem z e = ∈∈ₛ {a = z} {b = ⁅ x , y ⁆} .snd (pairing-ax x y z .snd ∣ e ∣₁)

  -- =================================================================
  -- THE CLOSURE.  Given the four closures the master already carries
  -- (numK0, sucK, pairK, and transK which is Ktr) plus the ONE new
  -- hypothesis finSetK, envConsK builds.  MEASURED: exit 0.
  -- =================================================================

  module EnvClosure
    (numK0 : ⟨ # 0 ∈ fst K ⟩)
    (sucK : (a : V ℓ) → ⟨ a ∈ fst K ⟩ → ⟨ sucV a ∈ fst K ⟩)
    (pairK : (a b : V ℓ) → ⟨ a ∈ fst K ⟩ → ⟨ b ∈ fst K ⟩ → ⟨ pr a b ∈ fst K ⟩)
    (finSetK : (n : ℕ) (h : Fin n → V ℓ)
             → ((i : Fin n) → ⟨ h i ∈ fst K ⟩) → ⟨ finSet n h ∈ fst K ⟩)
    where

    -- Every numeral is in K, by numK0 and sucK alone.  The master's
    -- numK0..numK11 are twelve instances; this is the general form,
    -- DERIVED, not a new hypothesis (C-38).
    numK : (n : ℕ) → ⟨ # n ∈ fst K ⟩
    numK zero    = numK0
    numK (suc n) = sucK (# n) (numK n)

    env-entry : {k : ℕ} (g : Fin k → V ℓ) (i : Fin k)
              → ⟨ pr (# (toℕ i)) (g i) ∈ env g ⟩
    env-entry g i = ∣ lift i , refl ∣₁

    giK : {k : ℕ} (g : Fin k → V ℓ) (i : Fin k)
        → ⟨ env g ∈ fst K ⟩ → ⟨ g i ∈ fst K ⟩
    giK g i envgK = prK (# (toℕ i)) (g i) (Ktr (env-entry g i) envgK) .snd

    envConsK : {k : ℕ} (g : Fin k → V ℓ) (x : V ℓ)
             → ⟨ env g ∈ fst K ⟩ → ⟨ x ∈ fst K ⟩
             → ⟨ env (cons x g) ∈ fst K ⟩
    envConsK g x envgK xK =
      finSetK (suc _) (λ j → pr (# (toℕ j)) (cons x g j))
        (λ { zero    → pairK (# 0) x numK0 xK
           ; (suc i) → pairK (sucV (# (toℕ i))) (g i)
                         (sucK (# (toℕ i)) (numK (toℕ i))) (giK g i envgK) })

  -- =================================================================
  -- The three consK-* honest forms, closed by envConsK.  These are
  -- [LJ-1.258]'s module ConsK with the hypothesis replaced by the
  -- derived term.  MEASURED: exit 0.
  -- =================================================================

  module ConsKClosed
    (numK0 : ⟨ # 0 ∈ fst K ⟩)
    (sucK : (a : V ℓ) → ⟨ a ∈ fst K ⟩ → ⟨ sucV a ∈ fst K ⟩)
    (pairK : (a b : V ℓ) → ⟨ a ∈ fst K ⟩ → ⟨ b ∈ fst K ⟩ → ⟨ pr a b ∈ fst K ⟩)
    (finSetK : (n : ℕ) (h : Fin n → V ℓ)
             → ((i : Fin n) → ⟨ h i ∈ fst K ⟩) → ⟨ finSet n h ∈ fst K ⟩)
    where

    open EnvClosure numK0 sucK pairK finSetK

    consK-forall : (γ' : Vec S 2) → (ya yc a ar c E z x e' : S)
                 → {k : ℕ} (g : Fin k → V ℓ)
                 → fst z ≡ env g
                 → ⟨ fst z ∈ fst K ⟩ → ⟨ fst x ∈ fst K ⟩
                 → ⟨ (e' ∷ x ∷ z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ') ⊨ᵐ
                     consAtL zero (suc zero) (suc (suc zero)) ⟩
                 → ⟨ fst e' ∈ fst K ⟩
    consK-forall γ' ya yc a ar c E z x e' g zg zK xK h =
      subst (λ w → ⟨ w ∈ fst K ⟩) (sym e'eq)
        (envConsK g (fst x) (subst (λ w → ⟨ w ∈ fst K ⟩) zg zK) xK)
      where
      e'eq : fst e' ≡ env (cons (fst x) g)
      e'eq = subst ⟨_⟩ (consAtL-adequate zero (suc zero) (suc (suc zero))
               (e' ∷ x ∷ z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ') g zg) h

    consK-allin : (γ' : Vec S 2) → (E ya yc b a ar c z w x e' : S)
                → {k : ℕ} (g : Fin k → V ℓ)
                → fst z ≡ env g
                → ⟨ fst z ∈ fst K ⟩ → ⟨ fst x ∈ fst K ⟩
                → ⟨ (e' ∷ x ∷ w ∷ z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨ᵐ
                    consAtL zero (suc zero) (suc (suc (suc zero))) ⟩
                → ⟨ fst e' ∈ fst K ⟩
    consK-allin γ' E ya yc b a ar c z w x e' g zg zK xK h =
      subst (λ w → ⟨ w ∈ fst K ⟩) (sym e'eq)
        (envConsK g (fst x) (subst (λ w → ⟨ w ∈ fst K ⟩) zg zK) xK)
      where
      e'eq : fst e' ≡ env (cons (fst x) g)
      e'eq = subst ⟨_⟩ (consAtL-adequate zero (suc zero) (suc (suc (suc zero)))
               (e' ∷ x ∷ w ∷ z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') g zg) h

    -- consK-exist carries the extra conjunct e' ∈ ya, so it closes from
    -- the site fact ya ∈ K by transitivity alone; its consAtL conjunct
    -- is dead weight ([LJ-1.151]'s valK defect).  This is the field's
    -- SECOND defect, named by [LJ-1.258] section 3 (C-36).
    consK-exist : (γ' : Vec S 2) → (ya yc a ar c E z x e' : S)
                → ⟨ fst ya ∈ fst K ⟩
                → ⟨ (e' ∷ x ∷ z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ') ⊨ᵐ
                    consAtL zero (suc zero) (suc (suc zero))
                    ∧̇ (var zero ∈̇ var (suc (suc (suc (suc zero))))) ⟩
                → ⟨ fst e' ∈ fst K ⟩
    consK-exist γ' ya yc a ar c E z x e' yaK h =
      Ktr (h .snd) yaK

-- ===================================================================
-- The concrete instance: K = Lset α as an element of L.
-- ===================================================================

levelK : (α : V ℓ) → IsOrd α → S
levelK α o = Lset α , isL-Lset α o

module AtLevel (α : V ℓ) (o : IsOrd α) =
  Fact (levelK α o) (layer-trans (Lset-layer α))

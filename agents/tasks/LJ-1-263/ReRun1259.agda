{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.263] re-run of ProbeLJ1259 against the MASTER.  The local
-- `EnvClosure` copy (and its `prK`) is removed; `envConsK` comes from
-- `L.Coding.Key` (C-45).  The three `consK-*` are unchanged and sit on
-- the master's closure.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-263.ReRun1259 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _∈̇_; _∧̇_ )
open import FOL.Semantics using ( _^_ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; isTransV; Lset; Lset-layer; layer-trans )
open import L.Axioms.Basic {ℓ} using ( isL-Lset; finSet )
open import L.Coding.Key {ℓ} lem using ( module EnvClosure )
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

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _⊨ᵐ_ )

-- ===================================================================
-- The env closure, now from the master.  No tower is named (DD4).
-- ===================================================================

module Fact (K : S) (Ktr : isTransV (fst K)) where

  module ConsKClosed
    (numK0 : ⟨ # 0 ∈ fst K ⟩)
    (sucK : (a : V ℓ) → ⟨ a ∈ fst K ⟩ → ⟨ sucV a ∈ fst K ⟩)
    (pairK : (a b : V ℓ) → ⟨ a ∈ fst K ⟩ → ⟨ b ∈ fst K ⟩ → ⟨ pr a b ∈ fst K ⟩)
    (finSetK : (n : ℕ) (h : Fin n → V ℓ)
             → ((i : Fin n) → ⟨ h i ∈ fst K ⟩) → ⟨ finSet n h ∈ fst K ⟩)
    where

    open EnvClosure (fst K) Ktr numK0 sucK pairK finSetK

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
    -- the site fact ya ∈ K by transitivity alone.
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

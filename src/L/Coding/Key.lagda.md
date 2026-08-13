# The split key, and its stage

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Coding.Key {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import FOL.Manipulation.Relabelling using ( embed )
open import FOL.Manipulation.Parameters using ( constantsFo; absFo )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; module VCode )
open import V.Model {ℓ} using ( ∈sucV-inl )
open import L.Constructible {ℓ} using ( IsOrd; Lset; 𝒟ₒ; Lset-mono )
open import L.Axioms.Basic {ℓ}
  using ( Lset-suc; pr∈Lset-suc; finSet; module FinOf )
open import L.Coding.Environment {ℓ} using ( env )
open import L.Choice.Name {ℓ} lem using ( numeral∈limit; code∈limit )
open import L.Ordinal.StageArith {ℓ} lem using ( sucIter; sucIter-ord )

open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Data.FinData using ( toℕ )
open import Cubical.Data.Vec using ( lookup )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; ∈∈ₛ; ∈ₛ⟪_⟫↪_; ∈-asFiber )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( #_; ω; sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- A stage function and the five facts the key's bound uses.  Nothing here
-- names a tower.  The key is the arity, the code of the parameter-free
-- formula, and the parameter environment, and the bound mentions neither the
-- formula's depth nor the number of parameters.
module KeyOver
  (T : S → S)
  (T-mono : {α β : S} → ⟨ β ∈ˢ α ⟩ → {x : S} → ⟨ x ∈ˢ T β ⟩ → ⟨ x ∈ˢ T α ⟩)
  (T-pr : (σ x y : S) → ⟨ x ∈ˢ T σ ⟩ → ⟨ y ∈ˢ T σ ⟩
        → ⟨ pr x y ∈ˢ T (sucV (sucV σ)) ⟩)
  (T-fin : (σ : S) → IsOrd σ → (k : ℕ) (h : Fin k → S)
         → ((i : Fin k) → ⟨ h i ∈ˢ T σ ⟩) → ⟨ finSet k h ∈ˢ T (sucV σ) ⟩)
  (T-num : (k : ℕ) → ⟨ (# k) ∈ˢ T ω ⟩)
  (T-code : ∀ {m} (χ : Formula (⊥* {ℓ}) m) → ⟨ VCode.⌜ embed χ ⌝ ∈ˢ T ω ⟩)
  where

  -- A member of the ω-stage sits in every finite iterate above σ once ω ∈ σ.
  fromω : (σ : S) → ⟨ ω ∈ˢ σ ⟩ → (d : ℕ) (x : S)
        → ⟨ x ∈ˢ T ω ⟩ → ⟨ x ∈ˢ T (sucIter (suc d) σ) ⟩
  fromω σ ω∈ zero    x h = T-mono {α = sucV σ} {β = ω} (∈sucV-inl ω∈) {x = x} h
  fromω σ ω∈ (suc d) x h =
    T-mono {α = sucIter (suc (suc d)) σ} {β = ω}
      (∈sucV-inl (fromω′ d)) {x = x} h
    where
    fromω′ : (e : ℕ) → ⟨ ω ∈ˢ sucIter (suc e) σ ⟩
    fromω′ zero    = ∈sucV-inl ω∈
    fromω′ (suc e) = ∈sucV-inl (fromω′ e)

  -- The parameter component is a SEQUENCE and never a finite set.  A finite
  -- set keeps no index, and the reading substitutes BY POSITION.
  paramEnv : {k : ℕ} → (Fin k → S) → S
  paramEnv h = env h

  -- Three stages, whatever k is: the index pairs cost two, the span one.
  paramEnv∈ : (σ : S) → IsOrd σ → ⟨ ω ∈ˢ σ ⟩ → (k : ℕ) (h : Fin k → S)
            → ((i : Fin k) → ⟨ h i ∈ˢ T σ ⟩)
            → ⟨ paramEnv h ∈ˢ T (sucIter 3 σ) ⟩
  paramEnv∈ σ oσ ω∈ k h hm =
    T-fin (sucIter 2 σ) (sucIter-ord 2 oσ) k
      (λ i → pr (# (toℕ i)) (h i)) pair∈
    where
    pair∈ : (i : Fin k) → ⟨ pr (# (toℕ i)) (h i) ∈ˢ T (sucIter 2 σ) ⟩
    pair∈ i = T-pr σ (# (toℕ i)) (h i)
      (T-mono {α = σ} {β = ω} ω∈ {x = # (toℕ i)} (T-num (toℕ i))) (hm i)

  -- THE KEY, and the bound is a FIXED iterate, uniform in χ and in k.
  splitKey : (n : ℕ) {k : ℕ} (χ : Formula (⊥* {ℓ}) (n + k)) (h : Fin k → S) → S
  splitKey n χ h = pr (# n) (pr VCode.⌜ embed χ ⌝ (paramEnv h))

  splitKey∈ : (σ : S) → IsOrd σ → ⟨ ω ∈ˢ σ ⟩ → (n : ℕ) {k : ℕ}
              (χ : Formula (⊥* {ℓ}) (n + k)) (h : Fin k → S)
            → ((i : Fin k) → ⟨ h i ∈ˢ T σ ⟩)
            → ⟨ splitKey n χ h ∈ˢ T (sucIter 7 σ) ⟩
  splitKey∈ σ oσ ω∈ n {k} χ h hm =
    T-pr (sucIter 5 σ) (# n) (pr VCode.⌜ embed χ ⌝ (paramEnv h))
      (fromω σ ω∈ 4 (# n) (T-num n))
      (T-pr (sucIter 3 σ) VCode.⌜ embed χ ⌝ (paramEnv h)
        (fromω σ ω∈ 2 VCode.⌜ embed χ ⌝ (T-code χ))
        (paramEnv∈ σ oσ ω∈ k h hm))

-- The L tower supplies the five facts.  One needs an adapter: the delivered
-- finite-family law is stated over fibers, and the generic law over members.
Lset-fin : (σ : S) → IsOrd σ → (k : ℕ) (h : Fin k → S)
         → ((i : Fin k) → ⟨ h i ∈ˢ Lset σ ⟩) → ⟨ finSet k h ∈ˢ Lset (sucV σ) ⟩
Lset-fin σ oσ k h hm =
  subst (λ w → ⟨ finSet k h ∈ˢ w ⟩) (sym (Lset-suc σ))
    (subst (λ w → ⟨ w ∈ˢ 𝒟ₒ (Lset σ) ⟩)
      (cong (finSet k) (funExt (λ i → fib i .snd)))
      (FinOf.finSet∈𝒟ₒ σ oσ k (λ i → fib i .fst)))
  where
  fib : (i : Fin k) → Σ[ m ∈ ⟪ Lset σ ⟫ ] (⟪ Lset σ ⟫↪ m ≡ h i)
  fib i = ∈-asFiber {a = h i} {b = Lset σ} (hm i)

open KeyOver Lset Lset-mono pr∈Lset-suc Lset-fin numeral∈limit code∈limit public

-- The delivered parameter split feeds the key unchanged, so the bound holds
-- for EVERY formula over the carrier.  `⌜_⌝` is not touched.
deliveredSplit : (σ : S) (φ : Formula ⟪ Lset σ ⟫ 1) → S
deliveredSplit σ φ = splitKey 1 (absFo {ℓz = ℓ} {n = 1} φ)
  (λ i → ⟪ Lset σ ⟫↪ (lookup i (constantsFo φ)))

deliveredSplit∈ : (σ : S) → IsOrd σ → ⟨ ω ∈ˢ σ ⟩ → (φ : Formula ⟪ Lset σ ⟫ 1)
                → ⟨ deliveredSplit σ φ ∈ˢ Lset (sucIter 7 σ) ⟩
deliveredSplit∈ σ oσ ω∈ φ = splitKey∈ σ oσ ω∈ 1 (absFo {ℓz = ℓ} {n = 1} φ)
  (λ i → ⟪ Lset σ ⟫↪ (lookup i (constantsFo φ)))
  (λ i → ∈∈ₛ {a = ⟪ Lset σ ⟫↪ (lookup i (constantsFo φ))} {b = Lset σ} .snd
           (∈ₛ⟪ Lset σ ⟫↪ (lookup i (constantsFo φ))))
```

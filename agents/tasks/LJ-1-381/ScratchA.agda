{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.381] scratch A.  MINIMIZE the step2 failure: the rename-back
-- along ρ through ⊨-rename, with ag, frameOf, lookup-inj only.  No
-- unfold, no leaves, no dialect equation.  If this is green, the
-- failure is in the combination, not in the rename-back leg.
--
-- ONE agda process under GHCRTS="-A64m -I0 -M8g".

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

open import FOL.ZFStructure using ( module hPropStructure; _↾_ )
open import FOL.Syntax using ( Formula; Term; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊤̇; ⊥̇; ∃̇_; ∀̇_; ∃̇∈; ∀̇∈ )
open import FOL.Manipulation.Relabelling using ( mapFo; mapTm )
import FOL.Absoluteness
open import FOL.Manipulation.Renaming using ( renameFo; renameTm; liftρ )
open import FOL.Manipulation.Relabelling using ( embed )
import FOL.Count
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆ ) renaming ( module InfinitySet to Inf )
open import Cubical.Data.Unit using ( tt* )
open import Cubical.Data.Nat using ( ℕ; zero; suc; _+_ )
open import Cubical.Data.Vec using ( Vec; lookup; _∷_; []; _++_ )

module LJ-1-381.ScratchA {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open Inf using ( #_; sucV )

import LJ-1-184.ProbeLJ1184A {ℓ} as P184
import LJ-1-297.ProbeLJ1297A {ℓ} lem as P1297A

module A = P184.Ambient
module P1241 = P1297A.P1241

SC : Type (ℓ-suc ℓ)
SC = A.R.SC

module AbsF = FOL.Absoluteness.Single 𝒮ᵥ P1297A.Full
  (λ {x} {y} → P1297A.Full-tr {x} {y})
open AbsF using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

module RenSat = FOL.Manipulation.Renaming.Sat
  (hPropAlgebra (ℓ-suc ℓ)) (𝒮ᵥ ↾ P1297A.Full) id

lookup-inj : {m n : ℕ} (i : Fin m) (xs : Vec SC m) (ys : Vec SC n)
           → lookup (P1241.inject+ i) (xs ++ ys) ≡ lookup i xs
lookup-inj zero    (x ∷ xs) ys = refl
lookup-inj (suc i) (x ∷ xs) ys = lookup-inj i xs ys

frameOf : Vec SC 14 → SC → SC → SC ^ 16
frameOf (w ∷ K ∷ δ₀ ∷ δ₁ ∷ δ₂ ∷ δ₃ ∷ δ₄ ∷ δ₅ ∷ δ₆ ∷ δ₇
         ∷ δ₈ ∷ δ₉ ∷ δ₁₀ ∷ δ₁₁ ∷ []) v g =
  w ∷ v ∷ g ∷ K ∷ δ₀ ∷ δ₁ ∷ δ₂ ∷ δ₃ ∷ δ₄ ∷ δ₅ ∷ δ₆ ∷ δ₇
    ∷ δ₈ ∷ δ₉ ∷ δ₁₀ ∷ δ₁₁ ∷ []

ag : (pre : Vec SC 14) (v g : SC)
   → RenSat.Agrees P1241.ρ (pre ++ (v ∷ g ∷ [])) (frameOf pre v g)
ag (w ∷ K ∷ δ₀ ∷ δ₁ ∷ δ₂ ∷ δ₃ ∷ δ₄ ∷ δ₅ ∷ δ₆ ∷ δ₇
     ∷ δ₈ ∷ δ₉ ∷ δ₁₀ ∷ δ₁₁ ∷ []) v g zero = refl
ag (w ∷ K ∷ δ₀ ∷ δ₁ ∷ δ₂ ∷ δ₃ ∷ δ₄ ∷ δ₅ ∷ δ₆ ∷ δ₇
     ∷ δ₈ ∷ δ₉ ∷ δ₁₀ ∷ δ₁₁ ∷ []) v g (suc zero) = refl
ag (w ∷ K ∷ δ₀ ∷ δ₁ ∷ δ₂ ∷ δ₃ ∷ δ₄ ∷ δ₅ ∷ δ₆ ∷ δ₇
     ∷ δ₈ ∷ δ₉ ∷ δ₁₀ ∷ δ₁₁ ∷ []) v g (suc (suc zero)) = refl
ag (w ∷ K ∷ δ₀ ∷ δ₁ ∷ δ₂ ∷ δ₃ ∷ δ₄ ∷ δ₅ ∷ δ₆ ∷ δ₇
     ∷ δ₈ ∷ δ₉ ∷ δ₁₀ ∷ δ₁₁ ∷ []) v g (suc (suc (suc zero))) = refl
ag (w ∷ K ∷ δ₀ ∷ δ₁ ∷ δ₂ ∷ δ₃ ∷ δ₄ ∷ δ₅ ∷ δ₆ ∷ δ₇
     ∷ δ₈ ∷ δ₉ ∷ δ₁₀ ∷ δ₁₁ ∷ []) v g (suc (suc (suc (suc i)))) =
  lookup-inj i (δ₀ ∷ δ₁ ∷ δ₂ ∷ δ₃ ∷ δ₄ ∷ δ₅ ∷ δ₆ ∷ δ₇
                  ∷ δ₈ ∷ δ₉ ∷ δ₁₀ ∷ δ₁₁ ∷ []) (v ∷ g ∷ [])

-- THE STEP UNDER TEST, at the REAL formula: base.
small : Formula (⊥* {ℓ-suc ℓ}) 16
small = P1241.base

-- the commutation stated at the ambient reading directly
sat-comm : (δ : Vec SC 16) (ψ : Formula (⊥* {ℓ-suc ℓ}) 16)
        → (δ ⊨ embed (renameFo P1241.ρ ψ))
          ≡ (δ ⊨ renameFo P1241.ρ (embed ψ))
sat-comm δ ψ = cong (λ χ → δ ⊨ χ) (emb-renP P1241.ρ ψ)
  where
  open import Cubical.Data.Empty as Empty
  mapTm-ren : {K K' : Type (ℓ-suc ℓ)} (f : K → K')
    {n m : ℕ} (ρ : Fin n → Fin m) (t : Term K n)
    → mapTm f (renameTm ρ t) ≡ renameTm ρ (mapTm f t)
  mapTm-ren f ρ (con k) = refl
  mapTm-ren f ρ (var i) = refl
  mapFo-ren : {K K' : Type (ℓ-suc ℓ)} (f : K → K')
    {n m : ℕ} (ρ : Fin n → Fin m) (φ : Formula K n)
    → mapFo f (renameFo ρ φ) ≡ renameFo ρ (mapFo f φ)
  mapFo-ren f ρ (t ∈̇ u) = cong₂ _∈̇_ (mapTm-ren f ρ t) (mapTm-ren f ρ u)
  mapFo-ren f ρ (t ≐ u) = cong₂ _≐_ (mapTm-ren f ρ t) (mapTm-ren f ρ u)
  mapFo-ren f ρ (φ ∧̇ ψ) = cong₂ _∧̇_ (mapFo-ren f ρ φ) (mapFo-ren f ρ ψ)
  mapFo-ren f ρ (φ ∨̇ ψ) = cong₂ _∨̇_ (mapFo-ren f ρ φ) (mapFo-ren f ρ ψ)
  mapFo-ren f ρ (φ ⇒̇ ψ) = cong₂ _⇒̇_ (mapFo-ren f ρ φ) (mapFo-ren f ρ ψ)
  mapFo-ren f ρ (¬̇ φ)   = cong ¬̇_ (mapFo-ren f ρ φ)
  mapFo-ren f ρ ⊤̇       = refl
  mapFo-ren f ρ ⊥̇       = refl
  mapFo-ren f ρ (∃̇ φ)   = cong ∃̇_ (mapFo-ren f (liftρ ρ) φ)
  mapFo-ren f ρ (∀̇ φ)   = cong ∀̇_ (mapFo-ren f (liftρ ρ) φ)
  mapFo-ren f ρ (∀̇∈ t φ) = cong₂ ∀̇∈ (mapTm-ren f ρ t) (mapFo-ren f (liftρ ρ) φ)
  mapFo-ren f ρ (∃̇∈ t φ) = cong₂ ∃̇∈ (mapTm-ren f ρ t) (mapFo-ren f (liftρ ρ) φ)
  emb-renP : {K : Type (ℓ-suc ℓ)} {n m : ℕ}
    (ρ : Fin n → Fin m) (φ : Formula (⊥* {ℓ-suc ℓ}) n)
    → embed (renameFo ρ φ) ≡ renameFo ρ (embed φ)
  emb-renP ρ φ = mapFo-ren Empty.rec* ρ φ

step2s : (pre : Vec SC 14) (v g : SC)
       → ⟨ (pre ++ (v ∷ g ∷ [])) ⊨
             renameFo P1241.ρ (embed small) ⟩
       → ⟨ frameOf pre v g ⊨
             embed small ⟩
step2s pre v g h = subst ⟨_⟩
  (RenSat.⊨-rename P1241.ρ
     (embed small)
     (pre ++ (v ∷ g ∷ [])) (frameOf pre v g) (ag pre v g)) h

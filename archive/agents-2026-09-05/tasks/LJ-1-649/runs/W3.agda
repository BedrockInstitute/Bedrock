{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.649]  W3, THE DECISIVE MINIATURE.  Do steps 2, 3 and 4 compose
-- into `levelIn` without a fifth fact?  This file answers that and
-- nothing else.  It is GREEN by construction: no hole, no postulate,
-- nothing in src/.
--
-- The frame is the FLOOR slice (runs/FLOOR.agda.txt), unchanged, with
-- the hole replaced by the assembly.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M2g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-649.runs.W3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; Lset )
open import L.Hull {ℓ} lem using ( module AtStage )
open import V.Collapse {ℓ} using ( module Collapse )

open import Cubical.Data.Sigma using ( Σ-syntax; _×_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; module InfinitySet )
open InfinitySet using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

module HullStage (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : S) (X⊆L : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  module ASt = AtStage lam ordλ
  module H = ASt.Hull X X⊆L ∅∈λ

  M : S
  M = H.T.Hull

  module C = Collapse M

  open H.T using ( Code; val )

  HullClosedLset : Type (ℓ-suc ℓ)
  HullClosedLset = (y : S) → ⟨ y ∈ˢ M ⟩ → ⟨ Lset y ∈ˢ M ⟩

  LsetCode : Type (ℓ-suc ℓ)
  LsetCode =
    (c : Code) → Σ[ d ∈ Code ] (fst (val d) ≡ Lset (fst (val c)))

  PiCommuteLset : Type (ℓ-suc ℓ)
  PiCommuteLset =
    (y : S) → ⟨ y ∈ˢ M ⟩ → C.π (Lset y) ≡ Lset (C.π y)

  step1 : (z : S) → ⟨ z ∈ˢ C.πX ⟩
        → ∥ Σ[ y ∈ S ] (⟨ y ∈ˢ M ⟩ × (C.π y ≡ z)) ∥₁
  step1 = C.πX-member

  levelin-from-steps : HullClosedLset → LsetCode → PiCommuteLset
                     → (δ : S) → IsOrd δ → ⟨ δ ∈ˢ C.πX ⟩ → ⟨ Lset δ ∈ˢ C.πX ⟩
  levelin-from-steps hcl lc pcl δ oδ δ∈πX =
    PT.rec (snd (Lset δ ∈ˢ C.πX)) go (step1 δ δ∈πX)
    where
    go : Σ[ y ∈ S ] (⟨ y ∈ˢ M ⟩ × (C.π y ≡ δ)) → ⟨ Lset δ ∈ˢ C.πX ⟩
    go (y , y∈M , e) =
      subst (λ z → ⟨ Lset z ∈ˢ C.πX ⟩) e
        (subst (λ w → ⟨ w ∈ˢ C.πX ⟩) (pcl y y∈M)
          (C.πX-intro (Lset y) (hcl y y∈M)))

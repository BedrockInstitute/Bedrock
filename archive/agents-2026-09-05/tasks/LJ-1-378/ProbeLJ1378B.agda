{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.378] probe B.  THE RESTRICTION, BUILT FROM `⊨-rename`.
--
-- `ProbeLJ1378A.agda` names the frame RESTRICTION as a hypothesis
-- (`rs`): the machine graph at φ₀'s seventeen-slot frame moves to the
-- two-slot pair.  This file BUILDS it from the delivered renaming
-- lemma (`src/FOL/Manipulation/Renaming.lagda.md:127`) and ONE
-- `refl`: the slot arithmetic `renameFo ρ₀ (LsetGraphAt {2} 0 1) ≡
-- LsetGraphAt {17} 0 3`, which the row builders' `sh2`-shifts were
-- designed to make definitional.
--
-- If this is green, the restriction leaves the named-obligation list:
-- it is DELIVERED machinery plus one definitional check.
--
-- ONE agda process under GHCRTS="-A64m -I0 -M8g".

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

open import FOL.ZFStructure using ( module hPropStructure; Transitive; _↾_ )
open import FOL.Syntax using ( Formula )
import FOL.Absoluteness
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆ ) renaming ( module InfinitySet to Inf )
open import Cubical.Data.Unit using ( tt* )
open import Cubical.Data.Vec using ( Vec; lookup; _∷_; [] )
open import FOL.Manipulation.Renaming using ( renameFo )

module LJ-1-378.ProbeLJ1378B {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒟ₒ )
open Inf using ( #_; sucV )

import LJ-1-184.ProbeLJ1184A {ℓ} as P184
import LJ-1-297.ProbeLJ1297A {ℓ} lem as P1297A
import LJ-1-238.GenSequence

module A = P184.Ambient

module GS = LJ-1-238.GenSequence {ℓ} lem P1297A.Full
  (λ {x} {y} → P1297A.Full-tr {x} {y})
  (λ k → # k , tt*) (λ k → refl)
  (λ a b → ⁅ fst a , fst b ⁆ , tt*) (λ a b → refl)
  (λ a → sucV (fst a) , tt*) (λ a → refl)

SC : Type (ℓ-suc ℓ)
SC = A.R.SC

module AbsF = FOL.Absoluteness.Single 𝒮ᵥ P1297A.Full
  (λ {x} {y} → P1297A.Full-tr {x} {y})
open AbsF using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

-- The renaming lemma, instantiated at the ambient reading.  The
-- algebra, structure and carrier are `AbsF`'s own.
module RenSat = FOL.Manipulation.Renaming.Sat
  (hPropAlgebra (ℓ-suc ℓ)) (𝒮ᵥ ↾ P1297A.Full) id

module Trio
  (DefAt : ∀ {n} → Fin n → Fin n → Formula SC n)
  (DefAt-in : (X : SC) → ∀ {n} (u w : Fin n) (γ : Vec SC n)
            → fst (lookup w γ) ≡ fst X
            → fst (lookup u γ) ≡ 𝒟ₒ (fst X)
            → ⟨ γ ⊨ DefAt u w ⟩)
  (DefAt-out : (X : SC) → ∀ {n} (u w : Fin n) (γ : Vec SC n) → GS.DefOK X
             → fst (lookup w γ) ≡ fst X
             → ⟨ γ ⊨ DefAt u w ⟩
             → fst (lookup u γ) ≡ 𝒟ₒ (fst X))
  where

  module Seq = GS.Body DefAt DefAt-in DefAt-out

  -- The restriction map: the value slot at zero, the ordinal slot at
  -- three, in the seventeen-slot frame (x ∷ u ∷ v ∷ g ∷ K ∷ δs).
  ρ₀ : Fin 2 → Fin 17
  ρ₀ zero = zero
  ρ₀ (suc zero) = suc (suc (suc zero))

  module Restr
    -- THE ONE SYNTACTIC HYPOTHESIS.  A `refl` run measured this
    -- equation up to ONE stuck subterm: renaming cannot push
    -- through the OPAQUE `DefAt` leaf
    -- (`renameFo (liftρ⁷ ρ₀) (DefAt zero (suc zero))`, where the
    -- seven lifts act as the identity on `zero` and `suc zero`).
    -- A naturality hypothesis `renameFo ρ (DefAt u w) ≡ DefAt
    -- (ρ u) (ρ w)` on the trio discharges exactly that subterm;
    -- everything else was DEFINITIONAL, by the row builders'
    -- `sh2`-shifts.
    (eq : Seq.LsetGraphAt {17} zero (suc (suc (suc zero)))
       ≡ renameFo ρ₀ (Seq.LsetGraphAt {2} zero (suc zero)))
    where

    ag : (x : SC) (frame : SC ^ 16)
       → RenSat.Agrees ρ₀ (x ∷ frame) (x ∷ lookup (suc (suc zero)) frame ∷ [])
    ag x frame zero = refl
    ag x frame (suc zero) = refl

    -- THE RESTRICTION, BUILT: `⊨-rename` along the two slots.
    restrict : (x : SC) (frame : SC ^ 16)
      → ⟨ (x ∷ frame) ⊨
            Seq.LsetGraphAt {17} zero (suc (suc (suc zero))) ⟩
      → ⟨ (x ∷ lookup (suc (suc zero)) frame ∷ []) ⊨
            Seq.LsetGraphAt {2} zero (suc zero) ⟩
    restrict x frame h =
      subst ⟨_⟩
        (RenSat.⊨-rename ρ₀ (Seq.LsetGraphAt {2} zero (suc zero))
           (x ∷ frame) (x ∷ lookup (suc (suc zero)) frame ∷ [])
           (ag x frame))
        (subst (λ ψ → ⟨ (x ∷ frame) ⊨ ψ ⟩) eq h)

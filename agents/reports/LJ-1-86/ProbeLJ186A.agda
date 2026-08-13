{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.86] probe A: AllCodes A is constructible, from its own delivered
-- certificate.
--
-- The separation machinery builds AllCodes A as a definable subset of a
-- stage: separateAt's sepElt is
--     carve ψ , 𝒟ₒ→isL σ oσ (carve ψ) (carve∈𝒟ₒ ψ)
-- (L.Axioms.Separation.lagda.md:293-294), with
--     carve∈𝒟ₒ ψ : ⟨ carve ψ ∈ 𝒟ₒ (Lset σ) ⟩
-- (:198-199) and
--     𝒟ₒ→isL : ... → ⟨ isL x ⟩
-- (L.Axioms.Basic.lagda.md:98).  So the carrier element AllCodes A carries
-- an isL certificate as its second projection, and the earliest-stage
-- function (L.Stage) extracts a NAMED ordinal lam with
--     IsOrd lam × fst (AllCodes A) ∈ Lset lam.
--
-- Untracked probe; one Agda process under GHCRTS="-A64m -I0 -M8g";
-- never committed.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ186A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( ZFStructure; module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; IsOrd; Lset )
open import L.Coding.CodeSet {ℓ} lem using ( AllCodes )
open import L.Stage {ℓ} lem using ( stage; stage-ord; stage-mem )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

Sʟ : Type (ℓ-suc ℓ)
Sʟ = ZFStructure.S 𝒮ʟ

-- THE ANSWER TO HALF 1.  AllCodes A is an element of L (its certificate
-- is built by the separation machinery), so the earliest-stage function
-- names the ordinal stage that contains it.
AllCodes-stage : (A : Sʟ) → Σ[ lam ∈ V ℓ ] (IsOrd lam × ⟨ fst (AllCodes A) ∈ˢ Lset lam ⟩)
AllCodes-stage A = stage (fst (AllCodes A)) ((AllCodes A) .snd)
                 , stage-ord (fst (AllCodes A)) ((AllCodes A) .snd)
                 , stage-mem (fst (AllCodes A)) ((AllCodes A) .snd)

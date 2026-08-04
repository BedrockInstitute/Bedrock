{-# OPTIONS --cubical --safe --guardedness #-}

-- [L3.31-P1] D-10 gate, mechanized.
--
-- Claim under test (p1-brief.md, the gate): "the +omega block absorbs the
-- unbounded-but-finite numeral ranks", so that a rank-bounded flat coding
-- lands the code SET inside Sset (+w d) even though the per-code offsets are
-- unbounded.
--
-- This file refutes the mechanism.  Membership in the omega-block factors
-- through ONE finite iterate, and the level at that iterate is transitive, so
-- the block-membership of a set forces a UNIFORM finite offset on all of its
-- members.  Nothing is absorbed that plain containment did not already absorb.
--
-- The argument is coding-independent: nothing below mentions the shape of a
-- code.  It therefore applies verbatim to any flat re-coding.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )

module ProbeD10 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) (A : V ℓ) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; 𝒟ₒ )
open import L.Rud.OrdArith {ℓ} lem using ( isLimit )
open import L.Rud.Step {ℓ} lem A using ( Sset; Sset-in; Sset-out; Sset-trans; step )
open import L.Rud.OrdBlocks {ℓ} lem using
  ( sucIter; +ω; +ω-out; +ω-mem; +ω-limit )
open import L.Rud.CodeSet {ℓ} lem A using ( module Codes )
open import L.Rud.CodePred {ℓ} lem A using ( module At )
open import L.Rud.SatTable {ℓ} lem A using ( module Coded; module TwoLimit )

open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- (1) A member of the omega-block level enters at one finite iterate.

blockFactor : (δ x : S) → ⟨ x ∈ˢ Sset (+ω δ) ⟩
            → ∥ Σ[ n ∈ ℕ ] ⟨ x ∈ˢ Sset (sucIter (suc n) δ) ⟩ ∥₁
blockFactor δ x h = PT.rec squash₁ atStage (Sset-out (+ω δ) x h)
  where
  Goal : Type (ℓ-suc ℓ)
  Goal = Σ[ n ∈ ℕ ] ⟨ x ∈ˢ Sset (sucIter (suc n) δ) ⟩
  atStage : Σ[ β ∈ S ] (⟨ β ∈ˢ +ω δ ⟩ × ⟨ x ∈ˢ step (Sset β) ⟩) → ∥ Goal ∥₁
  atStage (β , β∈ , x∈) = PT.map atIter (+ω-out δ β β∈)
    where
    atIter : Σ[ n ∈ ℕ ] ⟨ β ∈ˢ sucIter (suc n) δ ⟩ → Goal
    atIter (n , β∈n) = n , Sset-in (sucIter (suc n) δ) β x β∈n x∈

-- (2) Hence ALL of its members enter at that same finite iterate: the block
--     absorbs nothing, because the levels are transitive.

blockBound : (δ x : S) → ⟨ x ∈ˢ Sset (+ω δ) ⟩
           → ∥ Σ[ n ∈ ℕ ]
               ((y : S) → ⟨ y ∈ˢ x ⟩ → ⟨ y ∈ˢ Sset (sucIter (suc n) δ) ⟩) ∥₁
blockBound δ x h = PT.map go (blockFactor δ x h)
  where
  Goal : Type (ℓ-suc ℓ)
  Goal = Σ[ n ∈ ℕ ]
           ((y : S) → ⟨ y ∈ˢ x ⟩ → ⟨ y ∈ˢ Sset (sucIter (suc n) δ) ⟩)
  go : Σ[ n ∈ ℕ ] ⟨ x ∈ˢ Sset (sucIter (suc n) δ) ⟩ → Goal
  go (n , hx) = n , λ y y∈x → Sset-trans (sucIter (suc n) δ) {x = x} {y = y} y∈x hx

-- (3) At the code set: ONE offset would have to serve EVERY formula.
--     This is the exact statement the flat re-coding was dispatched to make
--     true, and it is a uniform-boundedness claim, not a per-code one.

codeBound : (C δ : S) (k : ℕ) → ⟨ Codes.codeSet C k ∈ˢ Sset (+ω δ) ⟩
          → ∥ Σ[ n ∈ ℕ ] ((φ : Formula ⟪ C ⟫ k)
              → ⟨ Codes.code C φ ∈ˢ Sset (sucIter (suc n) δ) ⟩) ∥₁
codeBound C δ k h = PT.map go (blockBound δ (Codes.codeSet C k) h)
  where
  Goal : Type (ℓ-suc ℓ)
  Goal = Σ[ n ∈ ℕ ] ((φ : Formula ⟪ C ⟫ k)
           → ⟨ Codes.code C φ ∈ˢ Sset (sucIter (suc n) δ) ⟩)
  go : Σ[ n ∈ ℕ ] ((y : S) → ⟨ y ∈ˢ Codes.codeSet C k ⟩
                 → ⟨ y ∈ˢ Sset (sucIter (suc n) δ) ⟩) → Goal
  go (n , bound) = n , λ φ → bound (Codes.code C φ) (Codes.code∈codeSet C k φ)

-- (4) The positive half of the gate.  At a LIMIT δ the DELIVERED nested coding
--     already lands the code set inside the ω-block: instantiate K3's two-limit
--     telescope at the outer level +ω δ, which holds δ by +ω-mem and is a limit
--     by +ω-limit.  Offset zero, no re-coding involved.

codeSet-in-block : (δ : S) → (ordδ : IsOrd δ) → (limδ : ⟨ isLimit δ ⟩)
                 → (C : S) → ⟨ C ∈ˢ Sset δ ⟩
                 → ⟨ Codes.codeSet C 1 ∈ˢ Sset (+ω δ) ⟩
codeSet-in-block δ ordδ limδ C C∈ =
  At.codeSet∈J (+ω δ) (+ω-limit δ ordδ) δ limδ (+ω-mem δ) C C∈ 1

-- (5) Hence BlockPow at a limit δ has exactly ONE hypothesis left, the coded
--     satisfaction relation over C at the level +ω δ.  The two-limit telescope
--     is not the obstruction once δ is a limit.

blockPow-at-limit : (δ : S) → (ordδ : IsOrd δ) → (limδ : ⟨ isLimit δ ⟩)
                  → (C : S) → (C∈ : ⟨ C ∈ˢ Sset δ ⟩) → (R : S)
                  → Coded.SatRelation (+ω δ) (+ω-limit δ ordδ) C R
                  → ⟨ 𝒟ₒ C ∈ˢ Sset (+ω δ) ⟩
blockPow-at-limit δ ordδ limδ C C∈ R sr =
  TwoLimit.two-limit-pow (+ω δ) (+ω-limit δ ordδ) δ limδ (+ω-mem δ) C C∈ R sr

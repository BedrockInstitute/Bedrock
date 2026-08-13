{-# OPTIONS --cubical --safe --guardedness #-}

-- DD25 review probe H8: THE MISSING TEMPLATE.
--
-- `EraseTransfer` (src/L/Condensation.lagda.md:273-294) stops at
-- Delta-0.  The adequacy connector moves a SIGMA-1 statement, so it
-- needs the same template one level up.  ProbeDD25H5 wrote that
-- transfer directly at the concrete `LevelHood0.Σ₂` and paid 129 s for
-- it.  This probe states the SAME mathematics with the formula
-- ABSTRACT, then instantiates once, which is what `EraseTransfer`
-- itself does and what P-u prescribes.
--
-- Nothing here calls `erase-Δ₀` and nothing needs an `erase-Σ₁`.
-- Sigma-1 is upward only, so the transfer is a function, not a path;
-- the two ends are still congs of `erase-inv`.
--
-- DD4: the module mentions no L syntax.  Both towers can instantiate
-- it, exactly as both instantiate `EraseTransfer`.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeDD25H8 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import FOL.Syntax using ( Formula )
open import FOL.LevyHierarchy using ( Δ₀; Σ₁ )
open import FOL.Manipulation.Parameters using ( countFo )
open import FOL.Manipulation.Relabelling using ( embed )
import FOL.Count
import FOL.Absoluteness
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.BoundedSubset {ℓ} lem using ( module LevelHood0 )
open import Cubical.Data.Vec using ( map )

open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

module Cnt = FOL.Count.Count {ℓ = ℓ-suc ℓ} S

-- =====================================================================
-- THE TEMPLATE.  `EraseTransfer` at Sigma-1.  The formula is abstract,
-- so no built tree unfolds anywhere in this module.
-- =====================================================================
module EraseTransferΣ₁ {m : ℕ} (φ : Formula S m) (p : countFo φ ≡ 0)
                        (s : Σ₁ φ) (γ : S ^ m) where
  σL₀ : Formula (⊥* {ℓ-suc ℓ}) m
  σL₀ = Cnt.erase φ p

  σL : Formula S m
  σL = embed σL₀

  σL≡ : σL ≡ φ
  σL≡ = Cnt.erase-inv φ p

  σL-eq : ⟨ γ ⊨ φ ⟩ ≡ ⟨ γ ⊨ σL ⟩
  σL-eq = cong (λ ψ → ⟨ γ ⊨ ψ ⟩) (sym σL≡)

  σL-eqᵛ : ⟨ map fst γ ⊨ᵛ φ ⟩ ≡ ⟨ map fst γ ⊨ᵛ σL ⟩
  σL-eqᵛ = cong (λ ψ → ⟨ map fst γ ⊨ᵛ ψ ⟩) (sym σL≡)

  -- The upward transfer at the erased spelling.  `σ₁-up` is taken at
  -- the ORIGINAL formula and its ORIGINAL certificate.
  σL-up : ⟨ γ ⊨ σL ⟩ → ⟨ map fst γ ⊨ᵛ σL ⟩
  σL-up h = transport σL-eqᵛ (AbsL.σ₁-up s γ (transport (sym σL-eq) h))

-- =====================================================================
-- THE INSTANTIATION.  Once, at the level-hood statement.
-- =====================================================================

module LH0 = LevelHood0
  zero zero zero zero zero zero zero zero zero zero zero zero zero zero
  zero zero zero zero zero zero zero zero zero zero zero zero zero zero

count-Σ₂ : countFo LH0.Σ₂ ≡ 0
count-Σ₂ = refl

module StmtTransfer (γ : S ^ 1) where
  module E = EraseTransferΣ₁ LH0.Σ₂ count-Σ₂ LH0.Σ₁-Σ₂ γ

  σL : Formula S 1
  σL = E.σL

  σL≡ : σL ≡ LH0.Σ₂
  σL≡ = E.σL≡

  σL-up : ⟨ γ ⊨ σL ⟩ → ⟨ map fst γ ⊨ᵛ σL ⟩
  σL-up = E.σL-up
